To generate the solver formulas in Python using cvc5 for verifying the Technology in Society Requirement, we need to assert that either **CS 181W** or **CS 182W** is taken as a Technology in Society (TiS) course. Here is the Python code to achieve this using the cvc5 solver:

```python
import cvc5
from cvc5 import Solver, Kind

# Initialize the solver
solver = Solver()

# Declare course variables
cs181w_units = solver.mkConst(cvc5.Sort.Boolean(), "cs181w_units")
cs182w_units = solver.mkConst(cvc5.Sort.boolean(), "cs182w_units")

# Technology in Society Requirement
technology_in_society_courses = [
    cs181w_units,
    cs182w_units
]

# Assert that at least one of the Technology in Society courses is taken
tis_formula = solver.mkTerm(Kind.OR, *technology_in_society_courses)
solver.assertFormula(tis_formula)

# Example to check solver status
result = solver.checkSat()

# Print the result of the solving process
print("Solver result for Technology in Society Requirement:", result)
```

### Explanation:
1. **Initialization**: We initialize the `Solver`.
2. **Declare Course Variables**: We declare `cs181w_units` and `cs182w_units` as boolean constants.
3. **Technology in Society Requirement**: We create a list of courses that fulfill the Technology in Society Requirement.
4. **Assert At Least One Course**: We use the cvc5 `mkTerm` method with `Kind.OR` to assert that at least one of `cs181w_units` or `cs182w_units` must be true.
5. **Check Solver**: We check if the constraints are satisfied using `checkSat`.
6. **Print Result**: We print the result to see if the constraints satisfy the requirements.

You can run the above Python code in an environment with cvc5 installed to verify if the Technology in Society Requirement is met. The use of `*technology_in_society_courses` in the `mkTerm` call ensures that the correct logical relationship (OR) is constructed to assert that taking any one of the listed courses is enough to satisfy the requirement.