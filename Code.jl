# ============================================================
# "Категорна логічна модель формальної верифікації коректності
#  запитів і цілісності даних у реляційних базах"
# ============================================================
using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphics
using DataFrames

# ============================================================
# 1. Категорна схема RBAC 
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
# 2. Інстанція бази даних I : S → Par(Set) 
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
# 3. Перевірка посилальної цілісності через pullback 
#    Для кожного зовнішнього ключа f : A → B будується pullback
#    вздовж I(f) та inc : PK(I(B)) ↪ I(B).
#    Цілісність збережена ⟺ p_A : P → I(A) є ізоморфізмом,
#    тобто Im(p_A) = I(A).
#    Порушники: I(A) \ Im(p_A) — записи без коректного образу в PK(I(B)).
# ============================================================
function check_fk_integrity(db)
  homs    = [:user_of_ur, :role_of_ur, :role_of_rp, :perm_of_rp, :res_of_rp]
  sources = [:UserRole,   :UserRole,   :RolePermission, :RolePermission, :RolePermission]
  targets = [:User,       :Role,       :Role,           :Permission,     :Resource]
  all_ok  = true

  for (h, src, tgt) in zip(homs, sources, targets)
    pk_range  = 1:nparts(db, tgt)          # PK(I(B))
    vals      = db[h]                       # I(f) : I(A) → I(B)
    src_parts = parts(db, src)             # I(A)

    # Pullback P = { (a,b) | I(f)(a) = b, b ∈ PK(I(B)) }
    P = [(a, vals[a]) for a in src_parts if vals[a] in pk_range]

    # Im(p_A) — образ проекції p_A : P → I(A)
    im_pA     = Set(a for (a, _) in P)

    # I(A) \ Im(p_A) — записи-порушники
    violators = setdiff(Set(src_parts), im_pA)

    if isempty(violators)
      println("  ✓ p_A є ізоморфізмом: $h → $tgt, цілісність збережена")
    else
      println("  ✗ p_A не є ізоморфізмом: $h → $tgt")
      println("    Записи-порушники I(A) \\ Im(p_A): ", collect(violators))
      all_ok = false
    end
  end
  return all_ok
end

println("=== Перевірка посилальної цілісності ===")
integrity_ok = check_fk_integrity(db)

# ============================================================
# 4. Профунктор Q : S^op × S_res → Set через коенд 
#    Коенд реалізується як множина класів еквівалентності свідків.
#    Свідок для пари (u,p) — набір записів (ur, rp) такий, що
#    user_of_ur(ur) = u, role_of_ur(ur) = role_of_rp(rp), perm_of_rp(rp) = p.
#    Різні свідки одного кортежу (u,p) ототожнюються в коенді.
#    Q[u,p] = true ⟺ клас еквівалентності свідків для (u,p) непорожній.
# ============================================================
function build_query_profunctor(db; resource_filter=nothing, action_filter=nothing)
  nU = nparts(db, :User)
  nP = nparts(db, :Permission)

  # witnesses[u,p] = множина свідків { (ur,rp) } для кортежу (u,p)
  witnesses = Dict{Tuple{Int,Int}, Set{Tuple{Int,Int}}}()
  for u in 1:nU, p in 1:nP
    witnesses[(u,p)] = Set{Tuple{Int,Int}}()
  end

  for ur in parts(db, :UserRole)
    u = db[ur, :user_of_ur]
    r = db[ur, :role_of_ur]
    for rp in incident(db, r, :role_of_rp)
      p   = db[rp, :perm_of_rp]
      res = db[rp, :res_of_rp]
      # застосування фільтрів WHERE (Означення 4.1)
      res_ok = isnothing(resource_filter) || db[res, :res_name] == resource_filter
      act_ok = isnothing(action_filter)   || db[p,   :action]   == action_filter
      if res_ok && act_ok
        push!(witnesses[(u,p)], (ur, rp))
      end
    end
  end

  # Q[u,p] = true ⟺ клас еквівалентності свідків непорожній (коенд)
  Q = falses(nU, nP)
  for u in 1:nU, p in 1:nP
    Q[u,p] = !isempty(witnesses[(u,p)])
  end
  return Q
end

Q = build_query_profunctor(db; resource_filter="FINANCE_DATA", action_filter="DELETE")

# ============================================================
# 5. Атрибутивна проекція Attr_input^op ⊗ Attr_res 
#    Будується незалежно від Q, виключно зі структури морфізмів схеми.
#    A[u,p] = true ⟺ ∃ ur,rp : user_of_ur(ur)=u ∧
#                               role_of_ur(ur)=role_of_rp(rp) ∧
#                               perm_of_rp(rp)=p
# ============================================================
function build_attr_projection(db)
  nU = nparts(db, :User)
  nP = nparts(db, :Permission)
  A  = falses(nU, nP)
  for ur in parts(db, :UserRole)
    u = db[ur, :user_of_ur]
    r = db[ur, :role_of_ur]
    for rp in incident(db, r, :role_of_rp)
      p = db[rp, :perm_of_rp]
      A[u,p] = true
    end
  end
  return A
end

A = build_attr_projection(db)

# ============================================================
# 6. Перевірка soundness: η існує ⟺ Q ⊆ A  
#    Для кожної пари (u,p) перевіряється комутативність квадрата
#    натуральності: якщо Q[u,p]=true, але A[u,p]=false,
#    то η_(u,p) не існує і запит не є sound.
# ============================================================
function check_soundness(db, Q, A)
  violations = Tuple{Int,Int}[]
  nU, nP = size(Q)
  for u in 1:nU, p in 1:nP
    if Q[u,p] && !A[u,p]
      push!(violations, (u,p))
    end
  end
  if isempty(violations)
    println("  ✓ η існує для всіх (u,p): Q ⊆ A, запит є sound")
    return true
  else
    for (u,p) in violations
      println("  ✗ η_($(db[u,:username]), $(db[p,:permission_name])) не існує: ",
              "квадрат натуральності не комутує")
    end
    return false
  end
end

println("\n=== Sound запит (FINANCE_DATA, DELETE) ===")
η_ok = check_soundness(db, Q, A)

# ============================================================
# 7. Контрприклад: некоректний запит 
#    Q_bad = декартовий добуток User × Permission,
#    оминає морфізми схеми через UserRole/RolePermission.
#    Для пар де A[u,p]=false: η не існує → запит не є sound.
# ============================================================
function build_unsound_query(db)
  nU = nparts(db, :User)
  nP = nparts(db, :Permission)
  return trues(nU, nP)
end

Q_bad = build_unsound_query(db)
println("\n=== Некоректний запит (контрприклад) ===")
η_bad = check_soundness(db, Q_bad, A)

# ============================================================
# 8. Демонстрація порушення цілісності через pullback 
#    Додається запис з неіснуючим user_id=999.
#    I(A) \ Im(p_A) явно вказує на запис-порушник.
# ============================================================
println("\n=== Порушення цілісності: додавання запису з user_id=999 ===")
add_part!(db, :UserRole; user_of_ur=999, role_of_ur=1)
check_fk_integrity(db)

# ============================================================
# 9. Вивід матриць Q та A
# ============================================================
function print_matrix(name, M, row_labels, col_labels)
  hdr = lpad(name, 14) * "  " * join(lpad.(col_labels, 16), " ")
  println(hdr)
  println(repeat("-", length(hdr)))
  for (i, rl) in enumerate(row_labels)
    row = lpad(rl, 14) * "  "
    for j in 1:length(col_labels)
      row *= lpad(M[i,j] ? "true" : "false", 16)
    end
    println(row)
  end
  println()
end

users = db[1:nparts(db,:User), :username]
perms = db[:, :permission_name]

println("\n=== Матриця A  (Attr_input^op ⊗ Attr_res) ===")
print_matrix("A", A, users, perms)

println("=== Матриця Q  (sound запит) ===")
print_matrix("Q", Q, users, perms)

println("=== Матриця Q_bad  (некоректний запит) ===")
print_matrix("Q_bad", Q_bad, users, perms)

println("=== Порушення η: пари де Q_bad ⊄ A ===")
for (i,u) in enumerate(users), (j,p) in enumerate(perms)
  if Q_bad[i,j] && !A[i,j]
    println("  η_($(u), $(p)) не існує — квадрат натуральності не комутує")
  end
end
