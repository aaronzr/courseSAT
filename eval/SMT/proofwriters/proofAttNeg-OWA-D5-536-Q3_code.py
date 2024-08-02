
from cvc5 import Solver, Kind

solver = Solver()
solver.setLogic("UF")  # Changed logic to support quantifiers

# Defining the sorts
Person = solver.mkUninterpretedSort("Person")

# Defining the functions
is_furry = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_furry")
is_big = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_big")
is_white = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_white")
is_kind = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_kind")
is_quiet = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_quiet")
is_smart = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_smart")
is_blue = solver.mkConst(solver.mkFunctionSort(Person, solver.getBooleanSort()), "is_blue")

Erin = solver.mkConst(Person, "Erin")
Bob = solver.mkConst(Person, "Bob")
Gary = solver.mkConst(Person, "Gary")
Harry = solver.mkConst(Person, "Harry")

# Declaring variable for quantified statements
X = solver.mkVar(Person, "X")

# Translating each statement:
stmt1 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X), 
                      solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.APPLY_UF, is_furry, X), solver.mkTerm(Kind.APPLY_UF, is_big, X)))
solver.assertFormula(stmt1)

stmt2 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X), 
                      solver.mkTerm(Kind.IMPLIES,
                                    solver.mkTerm(Kind.AND, 
                                                  solver.mkTerm(Kind.APPLY_UF, is_white, X),
                                                  solver.mkTerm(Kind.APPLY_UF, is_kind, X)),
                                    solver.mkTerm(Kind.APPLY_UF, is_quiet, X)))
solver.assertFormula(stmt2)

stmt3 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X),
                      solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.APPLY_UF, is_kind, X), solver.mkTerm(Kind.APPLY_UF, is_smart, X)))
solver.assertFormula(stmt3)

stmt4 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X),
                      solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.APPLY_UF, is_quiet, X), solver.mkTerm(Kind.APPLY_UF, is_smart, X)))
solver.assertFormula(stmt4)

stmt5 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X),
                      solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.APPLY_UF, is_kind, X), solver.mkTerm(Kind.APPLY_UF, is_white, X)))
solver.assertFormula(stmt5)

stmt6 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X),
                      solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND,
                                                                solver.mkTerm(Kind.APPLY_UF, is_white, X),
                                                                solver.mkTerm(Kind.APPLY_UF, is_quiet, X)),
                                     solver.mkTerm(Kind.APPLY_UF, is_blue, X)))
solver.assertFormula(stmt6)

stmt7 = solver.mkTerm(Kind.FORALL, solver.mkTerm(Kind.VARIABLE_LIST, X),
                      solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND,
                                                                solver.mkTerm(Kind.APPLY_UF, is_smart, X),
                                                                solver.mkTerm(Kind.APPLY_UF, is_blue, X)),
                                     solver.mkTerm(Kind.APPLY_UF, is_furry, X)))
solver.assertFormula(stmt7)

stmt8 = solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.APPLY_UF, is_quiet, Erin),
                      solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, is_kind, Erin)))
solver.assertFormula(stmt8)

stmt9 = solver.mkTerm(Kind.APPLY_UF, is_big, Bob)
solver.assertFormula(stmt9)

stmt10 = solver.mkTerm(Kind.APPLY_UF, is_quiet, Bob)
solver.assertFormula(stmt10)

stmt11 = solver.mkTerm(Kind.APPLY_UF, is_smart, Bob)
solver.assertFormula(stmt11)

stmt12 = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, is_kind, Erin))
solver.assertFormula(stmt12)

stmt13 = solver.mkTerm(Kind.APPLY_UF, is_quiet, Erin)
solver.assertFormula(stmt13)

stmt14 = solver.mkTerm(Kind.APPLY_UF, is_big, Gary)
solver.assertFormula(stmt14)

stmt15 = solver.mkTerm(Kind.APPLY_UF, is_kind, Harry)
solver.assertFormula(stmt15)

# Test Statement: "Harry is smart."
test_stmt = solver.mkTerm(Kind.APPLY_UF, is_smart, Harry)

# Checking the test statement
solver.push()
solver.assertFormula(solver.mkTerm(Kind.NOT, test_stmt))
result = solver.checkSat()

if result.isUnsat():
    print("The test statement 'Harry is smart.' is satisfied.")
else:
    print("The test statement 'Harry is smart.' is not satisfied.")
solver.pop()
