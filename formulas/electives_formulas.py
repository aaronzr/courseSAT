
import cvc5

# Create a solver instance
solver = cvc5.Solver()

# Define kinds
Kind = cvc5.Kind

# Create the constraint
cs_129_constraint = solver.mkTerm(
    Kind.NOT, solver.mkTerm(
        Kind.EQUAL, solver.mkString("CS 129"), solver.mkString("CS 229")
    )
)

# Optionally, print or use the constraint
print(cs_129_constraint)
