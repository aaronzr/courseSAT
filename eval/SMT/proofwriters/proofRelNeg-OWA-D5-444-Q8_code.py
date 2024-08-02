
import cvc5
from cvc5 import Kind

# Initialize solver
solver = cvc5.Solver()

# Set logic to support quantifiers
solver.setLogic("UF")

# Define sorts (types)
Entity = solver.mkUninterpretedSort("Entity")
BoolSort = solver.getBooleanSort()

# Define constants
bald_eagle = solver.mkConst(Entity, "bald_eagle")
rabbit = solver.mkConst(Entity, "rabbit")
cow = solver.mkConst(Entity, "cow")
mouse = solver.mkConst(Entity, "mouse")

# Define predicates/functions (unary and binary)
round_func = solver.mkConst(solver.mkFunctionSort([Entity], BoolSort), "round")
chases_func = solver.mkConst(solver.mkFunctionSort([Entity, Entity], BoolSort), "chases")
young_func = solver.mkConst(solver.mkFunctionSort([Entity], BoolSort), "young")
likes_func = solver.mkConst(solver.mkFunctionSort([Entity, Entity], BoolSort), "likes")
visits_func = solver.mkConst(solver.mkFunctionSort([Entity, Entity], BoolSort), "visits")
kind_func = solver.mkConst(solver.mkFunctionSort([Entity], BoolSort), "kind")
green_func = solver.mkConst(solver.mkFunctionSort([Entity], BoolSort), "green")

# Define contextual statements
statements = []

# Helper function to apply unary functions
def apply_unary(func, arg):
    return solver.mkTerm(Kind.APPLY_UF, func, arg)

# Helper function to apply binary functions
def apply_binary(func, arg1, arg2):
    return solver.mkTerm(Kind.APPLY_UF, func, arg1, arg2)

# Helper function to create implies
def mkImplies(a, b):
    return solver.mkTerm(Kind.IMPLIES, a, b)

# 'If something is round then it chases the rabbit.'
x = solver.mkVar(Entity, "x")
stmt1_body = mkImplies(apply_unary(round_func, x), apply_binary(chases_func, x, rabbit))
stmt1 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, x), stmt1_body)
statements.append(stmt1)

# 'If something chases the cow then it is young.'
y = solver.mkVar(Entity, "y")
stmt2_body = mkImplies(apply_binary(chases_func, y, cow), apply_unary(young_func, y))
stmt2 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, y), stmt2_body)
statements.append(stmt2)

# 'If the bald eagle likes the rabbit and the rabbit chases the cow then the bald eagle does not visit the cow.'
stmt3 = mkImplies(
    solver.mkTerm(Kind.AND, apply_binary(likes_func, bald_eagle, rabbit), apply_binary(chases_func, rabbit, cow)), 
    solver.mkTerm(Kind.NOT, apply_binary(visits_func, bald_eagle, cow))
)
statements.append(stmt3)

# 'If the bald eagle chases the rabbit then the rabbit is round.'
stmt4 = mkImplies(apply_binary(chases_func, bald_eagle, rabbit), apply_unary(round_func, rabbit))
statements.append(stmt4)

# 'If something is young and it likes the rabbit then it is green.'
z = solver.mkVar(Entity, "z")
stmt5_body = mkImplies(
    solver.mkTerm(Kind.AND, apply_unary(young_func, z), apply_binary(likes_func, z, rabbit)), 
    apply_unary(green_func, z)
)
stmt5 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, z), stmt5_body)
statements.append(stmt5)

# 'If something is green then it is round.'
stmt6_body = mkImplies(apply_unary(green_func, z), apply_unary(round_func, z))
stmt6 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, z), stmt6_body)
statements.append(stmt6)

# 'If the rabbit likes the bald eagle then the bald eagle is round.'
stmt7 = mkImplies(apply_binary(likes_func, rabbit, bald_eagle), apply_unary(round_func, bald_eagle))
statements.append(stmt7)

# 'If something chases the bald eagle then it likes the bald eagle.'
w = solver.mkVar(Entity, "w")
stmt8_body = mkImplies(apply_binary(chases_func, w, bald_eagle), apply_binary(likes_func, w, bald_eagle))
stmt8 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, w), stmt8_body)
statements.append(stmt8)

# 'If something is green and it likes the cow then it visits the rabbit.'
v = solver.mkVar(Entity, "v")
stmt9_body = mkImplies(
    solver.mkTerm(Kind.AND, apply_unary(green_func, v), apply_binary(likes_func, v, cow)), 
    apply_binary(visits_func, v, rabbit)
)
stmt9 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, v), stmt9_body)
statements.append(stmt9)

# Assert basic facts
# 'The bald eagle chases the cow.'
statements.append(apply_binary(chases_func, bald_eagle, cow))

# 'The bald eagle likes the rabbit.'
statements.append(apply_binary(likes_func, bald_eagle, rabbit))

# 'The bald eagle visits the cow.'
statements.append(apply_binary(visits_func, bald_eagle, cow))

# 'The cow is not young.'
statements.append(solver.mkTerm(Kind.NOT, apply_unary(young_func, cow)))

# 'The mouse chases the rabbit.'
statements.append(apply_binary(chases_func, mouse, rabbit))

# 'The mouse likes the bald eagle.'
statements.append(apply_binary(likes_func, mouse, bald_eagle))

# 'The mouse likes the cow.'
statements.append(apply_binary(likes_func, mouse, cow))

# 'The mouse does not like the rabbit.'
statements.append(solver.mkTerm(Kind.NOT, apply_binary(likes_func, mouse, rabbit)))

# 'The rabbit chases the mouse.'
statements.append(apply_binary(chases_func, rabbit, mouse))

# 'The rabbit is kind.'
statements.append(apply_unary(kind_func, rabbit))

# 'The rabbit is young.'
statements.append(apply_unary(young_func, rabbit))

# 'The rabbit likes the cow.'
statements.append(apply_binary(likes_func, rabbit, cow))

# Test statement: 'The bald eagle is not round.'
test_statement = solver.mkTerm(Kind.NOT, apply_unary(round_func, bald_eagle))

# Add all statements to the solver
for stmt in statements:
    solver.assertFormula(stmt)

# Check the test statement
solver.assertFormula(test_statement)
result = solver.checkSat()

print(f"Is the test statement '{test_statement}' satisfiable? {result}")

if result.isUnsat():
    print("Test statement is unsatisfied.")
elif result.isSat():
    print("Test statement is satisfied.")
else:  # Result.UNKNOWN
    print("Could not determine the satisfaction of the test statement.")
