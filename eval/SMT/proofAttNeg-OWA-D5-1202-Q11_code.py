Certainly! Translating the given statements into CVC5 SMT formulas involves formalizing each statement in a logical formula format using Python. We'll be using CVC5's Python API for this purpose. Here's the translation for each of the contextual statements and the test statement:

```python
import cvc5

# Initialize solver
solver = cvc5.Solver()

# Define sorts
Bool = solver.mkBoolSort()

# Define variables
Dave_is_white = solver.mkConst(Bool, 'Dave_is_white')
Dave_is_rough = solver.mkConst(Bool, 'Dave_is_rough')
Erin_is_young = solver.mkConst(Bool, 'Erin_is_young')
Erin_is_white = solver.mkConst(Bool, 'Erin_is_white')
Erin_is_blue = solver.mkConst(Bool, 'Erin_is_blue')
Erin_is_nice = solver.mkConst(Bool, 'Erin_is_nice')
Anne_is_young = solver.mkConst(Bool, 'Anne_is_young')
Dave_is_not_nice = solver.mkConst(Bool, 'Dave_is_not_nice')
Fiona_is_blue = solver.mkConst(Bool, 'Fiona_is_blue')
Fiona_is_rough = solver.mkConst(Bool, 'Fiona_is_rough')
Fiona_is_round = solver.mkConst(Bool, 'Fiona_is_round')

# Define predicates
is_big = solver.mkFuncDecl('is_big', Bool, Bool)
is_round = solver.mkFuncDecl('is_round', Bool, Bool)
is_rough = solver.mkFuncDecl('is_rough', Bool, Bool)
is_nice = solver.mkFuncDecl('is_nice', Bool, Bool)

# Contextual statements as CVC5 formulas

# 1. If Dave is white then Dave is rough.
stmt1 = solver.mkTerm(cvc5.Kinds.Implies, Dave_is_white, Dave_is_rough)

# 2. If Erin is young then Erin is white.
stmt2 = solver.mkTerm(cvc5.Kinds.Implies, Erin_is_young, Erin_is_white)

# 3. All blue, round people are big.
blue_round = solver.mkAnd(Fiona_is_blue, Fiona_is_round)
stmt3 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, blue_round, is_big))

# 4. Round, rough people are big.
round_rough = solver.mkAnd(Fiona_is_round, Fiona_is_rough)
stmt4 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, round_rough, is_big))

# 5. If someone is blue and not young then they are big.
blue_not_young = solver.mkAnd(Fiona_is_blue, solver.mkNot(Erin_is_young))
stmt5 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, blue_not_young, is_big))

# 6. All rough people are not nice.
stmt6 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, Fiona_is_rough, solver.mkNot(is_nice)))

# 7. All white people are round.
stmt7 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, Erin_is_white, Fiona_is_round))

# 8. If someone is nice and white then they are blue.
nice_white = solver.mkAnd(Erin_is_nice, Erin_is_white)
stmt8 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, nice_white, Fiona_is_blue))

# 9. Big, round people are rough.
big_round = solver.mkAnd(is_big(Fiona_is_blue), Fiona_is_round)
stmt9 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkTerm(cvc5.Kinds.Implies, big_round, Fiona_is_rough))

# 10. Anne is young.
stmt10 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), Anne_is_young)

# 11. Dave is not nice.
stmt11 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), solver.mkNot(Dave_is_not_nice))

# 12. Erin is blue.
stmt12 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), Erin_is_blue)

# 13. Erin is young.
stmt13 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), Erin_is_young)

# 14. Fiona is blue.
stmt14 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), Fiona_is_blue)

# 15. Fiona is rough.
stmt15 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), Fiona_is_rough)

# 16. Fiona is round.
stmt16 = solver.mkTerm(cvc5.Kinds.Forall, solver.mkVar(Bool, 'X'), Fiona_is_round)

# Add all statements to solver
solver.assertFormula(stmt1)
solver.assertFormula(stmt2)
solver.assertFormula(stmt3)
solver.assertFormula(stmt4)
solver.assertFormula(stmt5)
solver.assertFormula(stmt6)
solver.assertFormula(stmt7)
solver.assertFormula(stmt8)
solver.assertFormula(stmt9)
solver.assertFormula(stmt10)
solver.assertFormula(stmt11)
solver.assertFormula(stmt12)
solver.assertFormula(stmt13)
solver.assertFormula(stmt14)
solver.assertFormula(stmt15)
solver.assertFormula(stmt16)

# Test statement: Erin is not nice.
test_statement = solver.mkTerm(cvc5.Kinds.Not, Erin_is_nice)

# Check satisfiability
solver.assertFormula(test_statement)
result = solver.checkSat()
print(result)
```

This script initializes CVC5 and translates each of the contextual statements into a structured logical formula. Then, it checks whether the test statement "Erin is not nice" can be logically satisfied given all the provided contextual statements.

Please note that the CVC5 Python bindings can have slight variations based on the version of the library. Be sure to check the documentation for compatibility and syntax.