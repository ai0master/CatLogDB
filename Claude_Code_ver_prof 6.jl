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
# Очікуваний вивід:
#  ✗ η не існує: Q[charlie, full_access] = true, A = false
#  ✗ η не існує: Q[charlie, delete_finance] = true, A = false
#  ✗ η не існує: Q[alice, delete_finance] = true, A = false
#  ... → η_bad = false

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

users = db[:, :username]
perms = db[:, :permission_name]

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
