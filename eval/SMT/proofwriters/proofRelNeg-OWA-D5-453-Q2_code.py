
import cvc5

# Initialize the solver
solver = cvc5.Solver()

# Define sorts
boolean = solver.getBooleanSort()
animal = solver.mkUninterpretedSort("Animal")

# Define constants (animals)
rabbit = solver.mkConst(animal, "rabbit")
lion = solver.mkConst(animal, "lion")
tiger = solver.mkConst(animal, "tiger")
cat = solver.mkConst(animal, "cat")

# Define functions
is_young_sort = solver.mkFunctionSort(animal, boolean)  # Single argument function sort
is_young = solver.mkConst(is_young_sort, "is_young")

likes_sort = solver.mkFunctionSort([animal, animal], boolean)  # Multiple arguments function sort using a list
likes = solver.mkConst(likes_sort, "likes")

# Define terms
stmt14 = solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.APPLY_UF, is_young, rabbit))
stmt15 = solver.mkTerm(cvc5.Kind.APPLY_UF, likes, rabbit, lion)
stmt16 = solver.mkTerm(cvc5.Kind.APPLY_UF, likes, tiger, cat)

# Add additional logic or solver interactions below
solver.assertFormula(stmt14)
solver.assertFormula(stmt15)
solver.assertFormula(stmt16)

# Check satisfiability
result = solver.checkSat()
print(f"Result: {result}")
