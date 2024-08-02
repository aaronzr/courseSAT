
import cvc5
from cvc5 import Kind, Solver

solver = Solver()
solver.setOption("produce-models", "true")
bool_sort = solver.getBooleanSort()
bool_sort_sort = solver.mkFunctionSort(bool_sort, bool_sort)

# Define entities
bear = solver.mkConst(bool_sort, "bear")
cat = solver.mkConst(bool_sort, "cat")
dog = solver.mkConst(bool_sort, "dog")
rabbit = solver.mkConst(bool_sort, "rabbit")

# Define predicates
big = solver.mkConst(bool_sort_sort, "big")
visits = solver.mkConst(solver.mkFunctionSort([bool_sort, bool_sort], bool_sort), "visits")
chases = solver.mkConst(solver.mkFunctionSort([bool_sort, bool_sort], bool_sort), "chases")
eats = solver.mkConst(solver.mkFunctionSort([bool_sort, bool_sort], bool_sort), "eats")
round_ = solver.mkConst(bool_sort_sort, "round")
nice = solver.mkConst(bool_sort_sort, "nice")

# Helper variable for universally quantified formulas
x = solver.mkVar(bool_sort, "x")

# Statements
big_x_implies_not_visits_x_dog = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.APPLY_UF, big, x),
        solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, visits, x, dog))
    )
)
solver.assertFormula(big_x_implies_not_visits_x_dog)

visits_x_rabbit_implies_chases_x_rabbit = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.APPLY_UF, visits, x, rabbit),
        solver.mkTerm(Kind.APPLY_UF, chases, x, rabbit)
    )
)
solver.assertFormula(visits_x_rabbit_implies_chases_x_rabbit)

chases_x_cat_implies_round_x = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.APPLY_UF, chases, x, cat),
        solver.mkTerm(Kind.APPLY_UF, round_, x)
    )
)
solver.assertFormula(chases_x_cat_implies_round_x)

visits_x_cat_and_chases_x_dog_implies_round_x = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.AND, solver.mkTerm(Kind.APPLY_UF, visits, x, cat), solver.mkTerm(Kind.APPLY_UF, chases, x, dog)),
        solver.mkTerm(Kind.APPLY_UF, round_, x)
    )
)
solver.assertFormula(visits_x_cat_and_chases_x_dog_implies_round_x)

eats_x_cat_implies_not_big = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.APPLY_UF, eats, x, cat),
        solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, big, x))
    )
)
solver.assertFormula(eats_x_cat_implies_not_big)

round_x_implies_big = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.APPLY_UF, round_, x),
        solver.mkTerm(Kind.APPLY_UF, big, x)
    )
)
solver.assertFormula(round_x_implies_big)

chases_x_rabbit_implies_rabbit_chases_cat = solver.mkTerm(
    Kind.FORALL,
    solver.mkTerm(Kind.VARIABLE_LIST, x),
    solver.mkTerm(
        Kind.IMPLIES,
        solver.mkTerm(Kind.APPLY_UF, chases, x, rabbit),
        solver.mkTerm(Kind.APPLY_UF, chases, rabbit, cat)
    )
)
solver.assertFormula(chases_x_rabbit_implies_rabbit_chases_cat)

# Facts
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, round_, bear))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, visits, bear, rabbit))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, eats, cat, dog))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, visits, cat, bear))
solver.assertFormula(solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, eats, dog, cat)))
solver.assertFormula(solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.APPLY_UF, nice, dog)))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, round_, dog))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, visits, dog, bear))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, chases, rabbit, dog))
solver.assertFormula(solver.mkTerm(Kind.APPLY_UF, eats, rabbit, bear))

# Test Formula: The rabbit is round
test_formula = solver.mkTerm(Kind.APPLY_UF, round_, rabbit)
solver.assertFormula(test_formula)

# Check satisfiability
result = solver.checkSat()
print("Result of the test statement:", result)
