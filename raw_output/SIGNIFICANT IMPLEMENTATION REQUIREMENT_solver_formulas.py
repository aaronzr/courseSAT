Certainly! Based on the constraints described in the "SIGNIFICANT IMPLEMENTATION REQUIREMENT," let us construct the CVC5 solver formulas in Python code. Here is the implementation:

```python
import cvc5
from cvc5 import Kind

# Initialize the solver
solver = cvc5.Solver()

# List of course variables
courses = [
    'cs140', 'cs140e', 'cs143', 'cs144', 'cs145', 'cs148', 'cs151', 
    'cs190', 'cs210b', 'cs212', 'cs221', 'cs227b', 'cs231n', 'cs243', 
    'cs248', 'cs248a', 'cs341'
]

# List of corresponding course units
course_units = [
    'cs140_units', 'cs140e_units', 'cs143_units', 'cs144_units', 
    'cs145_units', 'cs148_units', 'cs151_units', 'cs190_units', 
    'cs210b_units', 'cs212_units', 'cs221_units', 'cs227b_units',
    'cs231n_units', 'cs243_units', 'cs248_units', 'cs248a_units', 
    'cs341_units'
]

# Define the formula that at least one course satisfies the Significant Implementation Requirement
significant_implementation = []

for course in courses:
    significant_implementation.append(solver.mkTerm(Kind.EQUAL, solver.mkVar(course, solver.getBooleanSort()), solver.mkTrue()))

# cs248 and cs248a are an exception and treated as one option
cs248_or_cs248a = solver.mkTerm(
    Kind.OR,
    solver.mkTerm(Kind.EQUAL, solver.mkVar('cs248', solver.getBooleanSort()), solver.mkTrue()),
    solver.mkTerm(Kind.EQUAL, solver.mkVar('cs248a', solver.getBooleanSort()), solver.mkTrue())
)
significant_implementation.append(cs248_or_cs248a)

# Assert the formula that at least one of them must be taken
solver.assertFormula(solver.mkTerm(Kind.OR, *significant_implementation))

# Ensure all courses must have at least 3 units (assuming solver metavariable for this)
three_units = solver.mkInteger(3)
for units in course_units:
    solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkVar(units, solver.getIntegerSort()), three_units))

# Example of usage:
# course_requirements = ['cs140', 'cs143', 'cs145']  # Given a student's course selections
# for req in course_requirements:
#     solver.assertFormula(solver.mkTerm(Kind.EQUAL, solver.mkVar(req, solver.getBooleanSort()), solver.mkTrue()))

# Checking the solver status
if solver.checkSat().isTrue():
    print("The constraints are satisfied.")
else:
    print("The constraints are not satisfied.")
```

This script uses the CVC5 solver to implement the following constraints based on the given "SIGNIFICANT IMPLEMENTATION REQUIREMENT":
1. At least one course from the specified list must be taken.
2. Course `cs248` and `cs248a` are treated as either-or options.
3. Ensures each course has at least 3 units.

To actually run the solver based on specific course enrollments, you would need to explicitly assert the courses as shown in the commented example.