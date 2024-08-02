
import cvc5
from cvc5 import Solver, Kind

solver = Solver()

# Declaration of functions and constants:
chases = solver.declareFun("chases", [solver.getStringSort(), solver.getStringSort()], solver.getBooleanSort())
nice = solver.declareFun("nice", [solver.getStringSort()], solver.getBooleanSort())
likes = solver.declareFun("likes", [solver.getStringSort(), solver.getStringSort()], solver.getBooleanSort())
sees = solver.declareFun("sees", [solver.getStringSort(), solver.getStringSort()], solver.getBooleanSort())
red = solver.declareFun("red", [solver.getStringSort()], solver.getBooleanSort())
young = solver.declareFun("young", [solver.getStringSort()], solver.getBooleanSort())
blue = solver.declareFun("blue", [solver.getStringSort()], solver.getBooleanSort())
big = solver.declareFun("big", [solver.getStringSort()], solver.getBooleanSort())

eagle = solver.mkString("bald_eagle")
bear = solver.mkString("bear")
cow = solver.mkString("cow")
dog = solver.mkString("dog")

# Universal quantifier variable
x = solver.mkVar(solver.getStringSort(), "x")

# 1. If something chases the bald eagle then it is nice.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES,
                                solver.mkTerm(Kind.APPLY_UF, chases, x, eagle),
                                solver.mkTerm(Kind.APPLY_UF, nice, x))))

# 2. If something likes the bald eagle and the bald eagle sees the dog then the bald eagle is red.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES, 
                                solver.mkTerm(Kind.AND, 
                                              solver.mkTerm(Kind.APPLY_UF, likes, x, eagle), 
                                              solver.mkTerm(Kind.APPLY_UF, sees, eagle, dog)), 
                                solver.mkTerm(Kind.APPLY_UF, red, eagle))))

# 3. If something is nice then it chases the cow.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES, 
                                solver.mkTerm(Kind.APPLY_UF, nice, x), 
                                solver.mkTerm(Kind.APPLY_UF, chases, x, cow))))

# 4. If something chases the cow then the cow is young.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES, 
                                solver.mkTerm(Kind.APPLY_UF, chases, x, cow), 
                                solver.mkTerm(Kind.APPLY_UF, young, cow))))

# 5. If something chases the cow then the cow likes the dog.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES, 
                                solver.mkTerm(Kind.APPLY_UF, chases, x, cow), 
                                solver.mkTerm(Kind.APPLY_UF, likes, cow, dog))))

# 6. If something sees the dog and the dog likes the cow then the cow chases the bald eagle.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES,
                                solver.mkTerm(Kind.AND,
                                              solver.mkTerm(Kind.APPLY_UF, sees, x, dog),
                                              solver.mkTerm(Kind.APPLY_UF, likes, dog, cow)),
                                solver.mkTerm(Kind.APPLY_UF, chases, cow, eagle))))

# 7. If something likes the dog then the dog likes the cow.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES, 
                                solver.mkTerm(Kind.APPLY_UF, likes, x, dog), 
                                solver.mkTerm(Kind.APPLY_UF, likes, dog, cow))))

# 8. Nice things are blue.
solver.assertFormula(
    solver.mkTerm(Kind.FORALL, 
                  solver.mkTerm(Kind.VARIABLE_LIST, x),
                  solver.mkTerm(Kind.IMPLIES,
                                solver.mkTerm(Kind.APPLY_UF, nice, x), 
                                solver.mkTerm(Kind.APPLY_UF, blue, x))))

# 9. The bald eagle chases the bear.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, chases, eagle, bear))

# 10. The bald eagle chases the cow.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, chases, eagle, cow))

# 11. The bald eagle likes the cow.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, likes, eagle, cow))

# 12. The bald eagle sees the cow.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, sees, eagle, cow))

# 13. The bear chases the cow.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, chases, bear, cow))

# 14. The bear is not young.
solver.assertFormula(solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, young, bear)))

# 15. The bear likes the bald eagle.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, likes, bear, eagle))

# 16. The cow is big.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, big, cow))

# 17. The cow sees the bear.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, sees, cow, bear))

# 18. The cow sees the dog.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, sees, cow, dog))

# 19. The dog likes the bald eagle.
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, likes, dog, eagle))

# Test statement: The cow is not nice.
solver.assertFormula(solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, nice, cow)))

# Check satisfaction
result = solver.checkSat()
print("Satisfiable:", result.isSat())
if result.isSat():
    model = solver.getModel()
    print("Model:")
    for decl in model.getDecls():
        print(decl, "=", model.getValue(decl))
