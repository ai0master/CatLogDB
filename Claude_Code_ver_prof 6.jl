# ============================================================
# Програма до статті:
# "Категорна логічна модель формальної верифікації коректності
#  запитів і цілісності даних у реляційних базах"
# Реалізує: Лістинг 5.1 + повний алгоритм верифікації (Розділ 5)
# Julia v1.12, Catlab.jl v0.16
# ============================================================

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphics
using DataFrames

# ============================================================
# 1. Категорна схема RBAC (Розділ 3, Рис. 1)
# ============================================================
@present RBACSchema(FreeSchema) begin
  (User, Role, Permission, Resource, UserRole, RolePermission)::Ob

  user_of_ur  :: Hom(UserRole, User)
  role_of_ur  :: Hom(UserRole, Role)
  role_of_rp  :: Hom(RolePermission, Role)
  perm_of_rp  :: Hom(RolePermission, Permission)
  res_of_rp   :: Hom(RolePermission, Resource)

  Name            :: AttrType
  username        :: Attr(User, Name)
  role_name       :: Attr(Role, Name)
  permission_name :: Attr(Permission, Name)
  res_name        :: Attr(Resource, Name)
  action          :: Attr(Permission, Name)
end

@acset_type RBAC(RBACSchema, index=[:user_of_ur, :role_of_ur,
                                    :role_of_rp, :perm_of_rp, :res_of_rp])

# ============================================================
# 2. Інстанція бази даних I : S → Par(Set) (Розділ 3, Табл. 2)
# ============================================================
db = RBAC{String}()

add_parts!(db, :User, 3;       username=["alice", "bob", "charlie"])
add_parts!(db, :Role, 2;       role_name=["admin", "finance"])
add_parts!(db, :Permission, 2; permission_name=["full_access", "delete_finance"],
                               action=["*", "DELETE"])
add_parts!(db, :Resource, 1;   res_name=["FINANCE_DATA"])
add_parts!(db, :UserRole, 3;   user_of_ur=[1,2,3], role_of_ur=[1,1,2])
add_parts!(db, :RolePermission, 2;
           role_of_rp=[1,2], perm_of_rp=[1,2], res_of_rp=[1,1])

# ============================================================
# 3. Етап 1: Перевірка посилальної цілісності (Par(Set))
# ============================================================
function check_fk_integrity(db)
  homs    = [:user_of_ur, :role_of_ur, :role_of_rp, :perm_of_rp, :res_of_rp]
  targets = [:User,       :Role,       :Role,        :Permission,  :Resource]
  all_ok  = true
  for (h, t) in zip(homs, targets)
    vals = db[h];  pk_range = 1:nparts(db, t)
    if any(v -> !(v in pk_range), vals)
      println("  ✗ FK порушено: $h → $t");  all_ok = false
    else
      println("  ✓ $h → $t")
    end
  end
  return all_ok
end

integrity_ok = check_fk_integrity(db)

# ============================================================
# 4. Етап 2: Профунктор Q : S^op × S_res → Set (coend)
# ============================================================
function build_query_profunctor(db)
  nU = nparts(db, :User);  nP = nparts(db, :Permission)
  Q  = falses(nU, nP)
  for ur in parts(db, :UserRole)
    u = db[ur, :user_of_ur];  r = db[ur, :role_of_ur]
    for rp in incident(db, r, :role_of_rp)
      p   = db[rp, :perm_of_rp]
      res = db[rp, :res_of_rp]
      if db[res, :res_name] == "FINANCE_DATA" && db[p, :action] == "DELETE"
        Q[u, p] = true
      end
    end
  end
  return Q
end

Q       = build_query_profunctor(db)
# ============================================================
# 4. Етап 2: Профунктор Q : S^op × S_res → Par(Set)  (coend)
# ============================================================
Q = build_query_profunctor(db)
coend_Q = vec(any(Q, dims=2))    # ∫^p Q(u,p)

# ============================================================
# 5. Attr-проекція — будується НЕЗАЛЕЖНО від Q,
#    прямо зі схеми через морфізми (Attr_input^op ⊗ Attr_res)
#    η_(u,p) існує ⟺ ∃ ur,rp : user_of_ur(ur)=u ∧
#                               role_of_ur(ur)=role_of_rp(rp) ∧
#                               perm_of_rp(rp)=p
# ============================================================
function build_attr_projection(db)
    nU = nparts(db, :User);  nP = nparts(db, :Permission)
    A  = falses(nU, nP)              # Attr_input^op ⊗ Attr_res
    for ur in parts(db, :UserRole)
        u = db[ur, :user_of_ur]
        r = db[ur, :role_of_ur]
        for rp in incident(db, r, :role_of_rp)
            p = db[rp, :perm_of_rp]
            A[u, p] = true           # морфізми схеми визначають A
        end
    end
    return A
end

A = build_attr_projection(db)        # незалежно від Q

# ============================================================
# 6. Перевірка soundness: η існує ⟺ Q ⊆ A  (Теорема 4.1)
#    Якщо Q[u,p]=true, але A[u,p]=false — η_(u,p) не існує,
#    натуральний квадрат не комутує → запит not sound.
# ============================================================
function check_soundness(db, Q, A)
    violations = Tuple{Int,Int}[]
    nU, nP = size(Q)
    for u in 1:nU, p in 1:nP
        if Q[u, p] && !A[u, p]       # η_(u,p) не існує
            push!(violations, (u, p))
        end
    end
    if isempty(violations)
        println("  ✓ η існує: Q ⊆ A — запит sound")
        return true
    else
        for (u, p) in violations
            println("  ✗ η не існує: Q[$(db[u,:username]),",
                    "$(db[p,:permission_name])] = true, A = false")
        end
        return false
    end
end

println("--- Sound запит (RBAC) ---")
η_ok = check_soundness(db, Q, A)

# ============================================================
# 7. Контрприклад: некоректний запит (Приклад 4.2)
#    Q_bad = декартовий добуток User × Permission,
#    оминає JOIN через UserRole/RolePermission.
#    Для пари (charlie, full_access): Q_bad=true, A=false
#    → η не існує → запит not sound.
# ============================================================
function build_unsound_query(db)
    nU = nparts(db, :User);  nP = nparts(db, :Permission)
    return trues(nU, nP)     # ∀u,p : Q_bad(u,p) = true
end

Q_bad = build_unsound_query(db)
println("--- Некоректний запит (контрприклад) ---")
η_bad = check_soundness(db, Q_bad, A)
# Генерація SVG квадратів природності (Рис. 2)
# Запускається після check_soundness; зберігає два файли:
#   naturality_sound.svg   — sound Q: всі квадрати комутують
#   naturality_unsound.svg — Q_bad: квадрати з порушеннями η

const C_BLUE  = "#3A5FA0"
const C_RED   = "#CC0000"
const C_GREEN = "#2A7A2A"
const C_LBLUE = "#EAF0FB"
const C_LRED  = "#FFE5E5"
const C_NAVY  = "#1A2F6A"

function _node!(io, cx, cy, l1, l2, ok::Bool)
    f = ok ? C_LBLUE : C_LRED
    s = ok ? C_BLUE  : C_RED
    print(io, "<rect x=\"$(cx-42)\" y=\"$(cy-19)\" width=\"84\" ")
    print(io, "height=\"38\" rx=\"5\" fill=\"$f\" stroke=\"$s\" ")
    println(io, "stroke-width=\"1.5\"/>")
    print(io, "<text x=\"$cx\" y=\"$(cy-5)\" text-anchor=\"middle\" ")
    println(io, "font-size=\"10\" font-weight=\"bold\" fill=\"$C_NAVY\">$l1</text>")
    print(io, "<text x=\"$cx\" y=\"$(cy+9)\" text-anchor=\"middle\" ")
    println(io, "font-size=\"9\" fill=\"#444\">$l2</text>")
end

function _arr!(io, x1,y1,x2,y2, lbl, ok::Bool, vert::Bool)
    col = ok ? C_BLUE : C_RED
    aid = ok ? "aok"  : "abad"
    dsh = ok ? ""     : " stroke-dasharray=\"5,3\""
    mx,my = (x1+x2)÷2, (y1+y2)÷2
    ox = vert ? -30 : 0;  oy = vert ? 0 : -7
    print(io, "<line x1=\"$x1\" y1=\"$y1\" x2=\"$x2\" y2=\"$y2\" ")
    print(io, "stroke=\"$col\" stroke-width=\"1.5\"$dsh ")
    println(io, "marker-end=\"url(#$aid)\"/>")
    print(io, "<text x=\"$(mx+ox)\" y=\"$(my+oy)\" ")
    println(io, "text-anchor=\"middle\" font-size=\"9\" ")
    println(io, "font-style=\"italic\" fill=\"$col\">$lbl</text>")
    if !ok && vert
        println(io, "<line x1=\"$(mx+ox-6)\" y1=\"$(my-6)\" ")
        println(io, "x2=\"$(mx+ox+6)\" y2=\"$(my+6)\" ")
        println(io, "stroke=\"$col\" stroke-width=\"2\"/>")
        println(io, "<line x1=\"$(mx+ox+6)\" y1=\"$(my-6)\" ")
        println(io, "x2=\"$(mx+ox-6)\" y2=\"$(my+6)\" ")
        println(io, "stroke=\"$col\" stroke-width=\"2\"/>")
    end
end

function _square!(io, u,p,u2,p2, q1,q2,a1,a2, eta_ok, x,y,W,H)
    xl,xr = x+60, x+W-60;  yt,yb = y+55, y+H-55
    _node!(io, xl,yt, "Q($u,$p)",   "= $q1", q1)
    _node!(io, xr,yt, "Q($u2,$p2)", "= $q2", true)
    _node!(io, xl,yb, "A($u,$p)",   "= $a1", a1)
    _node!(io, xr,yb, "A($u2,$p2)", "= $a2", true)
    _arr!(io, xl+43,yt, xr-43,yt, "Q(f,g)", true,  false)
    _arr!(io, xl+43,yb, xr-43,yb, "A(f,g)", true,  false)
    _arr!(io, xl,yt+19, xl,yb-19, "η_($u,$p)",   eta_ok, true)
    _arr!(io, xr,yt+19, xr,yb-19, "η_($u2,$p2)", true,   true)
    lbl = eta_ok ? "✓ комутує" : "✗ не комутує"
    col = eta_ok ? C_GREEN     : C_RED
    print(io, "<text x=\"$(x+W÷2)\" y=\"$(y+H-6)\" ")
    println(io, "text-anchor=\"middle\" font-size=\"10\" ")
    println(io, "font-weight=\"bold\" fill=\"$col\">$lbl</text>")
end

function naturality_svg(users, perms, A, Q; path="naturality.svg")
    viols = [(i,j) for i in 1:size(Q,1), j in 1:size(Q,2)
                   if Q[i,j] && !A[i,j]]
    examples = vcat([(1,1,false)], [(i,j,true) for (i,j) in viols])
    W,H,PAD = 300,250,24
    cols = 2;  rows = ceil(Int, length(examples)/cols)
    TW = cols*W + (cols+1)*PAD
    TH = rows*H + (rows+1)*PAD + 70
    open(path, "w") do io
        println(io, "<svg xmlns=\"http://www.w3.org/2000/svg\" ")
        println(io, "width=\"$TW\" height=\"$TH\" ")
        println(io, "font-family=\"Libertinus Serif, Georgia, serif\">")
        println(io, "<rect width=\"100%\" height=\"100%\" fill=\"white\"/>")
        # defs: arrowhead markers
        println(io, "<defs>")
        for (id,col) in [("aok",C_BLUE),("abad",C_RED)]
            print(io, "<marker id=\"$id\" markerWidth=\"8\" ")
            print(io, "markerHeight=\"8\" refX=\"7\" refY=\"3\" ")
            println(io, "orient=\"auto\">")
            println(io, "<path d=\"M0,0 L0,6 L8,3 z\" fill=\"$col\"/></marker>")
        end
        println(io, "</defs>")
        title = "Квадрати природності η : Q ⟹ A"
        print(io, "<text x=\"$(TW÷2)\" y=\"30\" text-anchor=\"middle\" ")
        println(io, "font-size=\"14\" font-weight=\"bold\" fill=\"$C_NAVY\">$title</text>")
        for (idx,(i,j,bad)) in enumerate(examples)
            c = (idx-1) % cols;  r = (idx-1) ÷ cols
            x = PAD + c*(W+PAD);  y = 70+PAD + r*(H+PAD)
            bc = bad ? "#FFE8E8" : "#E8F5E9"
            bs = bad ? C_RED     : C_GREEN
            print(io, "<rect x=\"$(x-5)\" y=\"$(y-5)\" ")
            print(io, "width=\"$(W+10)\" height=\"$(H+10)\" rx=\"7\" ")
            println(io, "fill=\"$bc\" stroke=\"$bs\" stroke-width=\"1.2\" opacity=\"0.5\"/>")
            _square!(io, users[i],perms[j],users[1],perms[1],
                     Q[i,j],Q[1,1],A[i,j],A[1,1],!bad,x,y,W,H)
        end
        println(io, "</svg>")
    end
    println("  ✓ SVG: $path")
end

users = db[:, :username]      # вектор імен користувачів
perms = db[:, :permission_name]  # вектор назв дозволів
naturality_svg(users, perms, A, A,     path="naturality_sound.svg")
naturality_svg(users, perms, A, Q_bad, path="naturality_unsound.svg")

# ============================================================
# 8. Вивід матриць Q та A (таблиці soundness)
# ============================================================
function print_matrix(name, M, row_labels, col_labels)
    hdr = lpad(name, 12) * "  " * join(lpad.(col_labels, 14), " ")
    println(hdr)
    println(repeat("-", length(hdr)))
    for (i, rl) in enumerate(row_labels)
        row = lpad(rl, 12) * "  "
        for j in 1:length(col_labels)
            cell = M[i,j] ? "  true" : " false"
            mark = (name != "A" && M[i,j] && !false) ? "" : ""
            row *= lpad(cell, 14)
        end
        println(row)
    end
    println()
end


println("=== Матриця A  (Attr_input^op ⊗ Attr_res) ===")
print_matrix("A", A, users, perms)

println("=== Матриця Q  (sound запит) ===")
print_matrix("Q_sound", Q, users, perms)

println("=== Матриця Q_bad  (некоректний запит) ===")
print_matrix("Q_bad", Q_bad, users, perms)

# Показуємо де Q_bad ⊄ A  →  η не існує
println("=== Порушення η (Q_bad[u,p]=true, A[u,p]=false) ===")
for (i,u) in enumerate(users), (j,p) in enumerate(perms)
    if Q_bad[i,j] && !A[i,j]
        println("  η_($(u),$(p)) не існує — квадрат природності не комутує")
    end

# ============================================================
# ============================================================
# 6. Негативний приклад: FK-порушення → AssertionError
# ============================================================
try
  add_part!(db, :UserRole; user_of_ur=999, role_of_ur=1)
catch e
  println("Par(Set) захист: ", typeof(e))
end
end

