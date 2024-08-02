
import cvc5
from cvc5 import Kind, Solver

# Initialize solver
solver = Solver()
# Change the logic to one that supports quantifiers
solver.setLogic("AUFLIA")

# Objects
cat = solver.mkConst(solver.getBooleanSort(), "cat")
mouse = solver.mkConst(solver.getBooleanSort(), "mouse")
bald_eagle = solver.mkConst(solver.getBooleanSort(), "bald_eagle")
rabbit = solver.mkConst(solver.getBooleanSort(), "rabbit")
someone = solver.mkConst(solver.getBooleanSort(), "someone")

# Predicates
likes_sort = solver.mkFunctionSort([solver.getBooleanSort(), solver.getBooleanSort()], solver.getBooleanSort())
likes = solver.mkConst(likes_sort, "likes")
visits_sort = solver.mkFunctionSort([solver.getBooleanSort(), solver.getBooleanSort()], solver.getBooleanSort())
visits = solver.mkConst(visits_sort, "visits")
chases_sort = solver.mkFunctionSort([solver.getBooleanSort(), solver.getBooleanSort()], solver.getBooleanSort())
chases = solver.mkConst(chases_sort, "chases")

# Function terms
likes_someone_cat = solver.mkTerm(Kind.APPLY_UF, likes, someone, cat)
visits_cat_mouse = solver.mkTerm(Kind.APPLY_UF, visits, cat, mouse)

# Create variables for quantification
x = solver.mkVar(solver.getBooleanSort(), "x")
y = solver.mkVar(solver.getBooleanSort(), "y")

# Bind the variables and create a universal quantification
bound_var_list = solver.mkTerm(Kind.VARIABLE_LIST, x, y)
forall_xy = solver.mkTerm(Kind.FORALL, bound_var_list,
                          solver.mkTerm(Kind.IMPLIES,
                                        solver.mkTerm(Kind.APPLY_UF, likes, x, y),
                                        solver.mkTerm(Kind.APPLY_UF, visits, x, y)))

# Assert the formula
solver.assertFormula(forall_xy)

# Additional assertions
visits_someone_mouse = solver.mkTerm(Kind.APPLY_UF, visits, someone, mouse)
visits_mouse_bald_eagle = solver.mkTerm(Kind.APPLY_UF, visits, mouse, bald_eagle)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES,
                                   solver.mkTerm(Kind.AND, visits_someone_mouse, likes_someone_cat),
                                   visits_mouse_bald_eagle))

likes_someone_bald_eagle = solver.mkTerm(Kind.APPLY_UF, likes, someone, bald_eagle)
visits_bald_eagle_mouse = solver.mkTerm(Kind.APPLY_UF, visits, bald_eagle, mouse)
chases_bald_eagle_mouse = solver.mkTerm(Kind.APPLY_UF, chases, bald_eagle, mouse)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES,
                                   solver.mkTerm(Kind.AND, likes_someone_bald_eagle, visits_bald_eagle_mouse),
                                   chases_bald_eagle_mouse))

is_cold = solver.mkConst(solver.getBooleanSort(), "is_cold")
likes_bald_eagle_cat = solver.mkTerm(Kind.APPLY_UF, likes, bald_eagle, cat)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, likes_bald_eagle_cat, is_cold))

visits_someone_bald_eagle = solver.mkTerm(Kind.APPLY_UF, visits, someone, bald_eagle)
chases_someone_bald_eagle = solver.mkTerm(Kind.APPLY_UF, chases, someone, bald_eagle)
chases_bald_eagle_cat = solver.mkTerm(Kind.APPLY_UF, chases, bald_eagle, cat)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES,
                                   solver.mkTerm(Kind.AND, visits_someone_bald_eagle, chases_someone_bald_eagle),
                                   chases_bald_eagle_cat))

chases_someone_cat = solver.mkTerm(Kind.APPLY_UF, chases, someone, cat)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, chases_someone_cat, likes_someone_cat))

is_blue = solver.mkConst(solver.getBooleanSort(), "is_blue")
is_kind = solver.mkConst(solver.getBooleanSort(), "is_kind")
solver.assertFormula(solver.mkTerm(Kind.IMPLIES,
                                   solver.mkTerm(Kind.AND, is_blue, is_kind),
                                   solver.mkTerm(Kind.APPLY_UF, likes, someone, rabbit)))

chases_someone_mouse = solver.mkTerm(Kind.APPLY_UF, chases, someone, mouse)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES,
                                   solver.mkTerm(Kind.AND, likes_someone_cat, chases_someone_mouse),
                                   likes_someone_bald_eagle))

solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_cold, visits_someone_mouse))

chases_bald_eagle_cat_2 = solver.mkTerm(Kind.APPLY_UF, chases, bald_eagle, cat)
solver.assertFormula(chases_bald_eagle_cat_2)

visits_bald_eagle_rabbit = solver.mkTerm(Kind.APPLY_UF, visits, bald_eagle, rabbit)
solver.assertFormula(visits_bald_eagle_rabbit)

is_green_cat = solver.mkConst(solver.getBooleanSort(), "is_green_cat")
solver.assertFormula(is_green_cat)

is_kind_cat = solver.mkConst(solver.getBooleanSort(), "is_kind_cat")
solver.assertFormula(is_kind_cat)

likes_cat_rabbit = solver.mkTerm(Kind.APPLY_UF, likes, cat, rabbit)
solver.assertFormula(likes_cat_rabbit)

chases_mouse_cat = solver.mkTerm(Kind.APPLY_UF, chases, mouse, cat)
solver.assertFormula(chases_mouse_cat)

likes_mouse_bald_eagle = solver.mkTerm(Kind.APPLY_UF, likes, mouse, bald_eagle)
solver.assertFormula(likes_mouse_bald_eagle)

likes_mouse_cat = solver.mkTerm(Kind.APPLY_UF, likes, mouse, cat)
solver.assertFormula(likes_mouse_cat)

visits_mouse_rabbit = solver.mkTerm(Kind.APPLY_UF, visits, mouse, rabbit)
solver.assertFormula(visits_mouse_rabbit)

likes_rabbit_cat = solver.mkTerm(Kind.APPLY_UF, likes, rabbit, cat)
solver.assertFormula(likes_rabbit_cat)

# Test statement
solver.assertFormula(visits_cat_mouse)

# Check SAT
result = solver.checkSat()
print(result)
