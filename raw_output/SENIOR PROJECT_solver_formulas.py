To accomplish this, we'll use CVC5's Python API to create formal constraints that represent the given course requirements. We'll start by importing the necessary CVC5 modules and defining the constraints to ensure that at least one of the senior project courses is selected with a minimum of 3 units. We'll also define the constraints for the mathematics and science requirements.

Here is a Python script using CVC5 to model these constraints:

```python
import pycvc5
from pycvc5 import Solver, Kind

# Initialize CVC5 Solver
solver = Solver()
solver.setLogic("QF_LIA")  # Setting the logic to Quantifier-Free Linear Integer Arithmetic

# Define the courses related to Senior Project and their units
senior_project_courses = [
    "cs191_units",
    "cs191w_units",
    "cs194_units",
    "cs194h_units",
    "cs194w_units",
    "cs210b_units",
    "cs294_units"
]

# Define course requirements
course_requirements = [
    "math19",
    "math20",
    "math21",
    "cs103",
    "cs109",
    "phys41",
    "phys43",
    ("math51", "math52", "math53", "math104", "math107", "math108", "math109", "math110", "math113", "cs205l", "cme100", "cme102", "cme104", "engr108"),
    ("cs157", "phil151")
]

# Define the total units required for Mathematics and Science
total_math_units = 26
total_science_units = 11

# Add variables for each course unit
course_units = {course: solver.mkConst(solver.getIntegerSort(), course + "_units") for course in senior_project_courses}
course_units.update({course: solver.mkConst(solver.getIntegerSort(), course + "_units") for course in
                     ["math19", "math20", "math21", "cs103", "cs109", "phys41", "phys43"]})
course_units.update({course: solver.mkConst(solver.getIntegerSort(), course + "_units") for courses in course_requirements if isinstance(courses, tuple) for course in courses})

# Constraints for required senior project courses (at least one with 3 or more units)
senior_project_constraint = solver.mkTerm(Kind.OR,
                                          *[solver.mkTerm(Kind.GEQ, course_units[course], solver.mkInteger(3)) for course in senior_project_courses])

solver.assertFormula(senior_project_constraint)

# Constraints for the other courses requirements
for requirement in course_requirements:
    if isinstance(requirement, tuple):
        or_terms = [solver.mkTerm(Kind.OR, solver.mkTerm(Kind.GEQ, course_units[course], solver.mkInteger(3))) for course in requirement]
        solver.assertFormula(solver.mkTerm(Kind.OR, *or_terms))
    else:
        solver.assertFormula(solver.mkTerm(Kind.GEQ, course_units[requirement], solver.mkInteger(3)))

# Constraints for the total mathematics units
math_courses = ["math19", "math20", "math21"] + [course for courses in course_requirements if isinstance(courses, tuple) and any("math" in c for c in courses) for course in courses]
math_units_sum = solver.mkTerm(Kind.ADD, *[course_units[course] for course in math_courses])
solver.assertFormula(solver.mkTerm(Kind.GEQ, math_units_sum, solver.mkInteger(total_math_units)))

# Constraints for the total science units
science_courses = ["phys41", "phys43"] + [course for courses in course_requirements if isinstance(courses, tuple) and any("phys" in c or "bio" in c or "chem" in c or "earthsys" in c for c in courses) for course in courses]
science_units_sum = solver.mkTerm(Kind.ADD, *[course_units[course] for course in science_courses])
solver.assertFormula(solver.mkTerm(Kind.GEQ, science_units_sum, solver.mkInteger(total_science_units)))

# Checking the constraints
if solver.checkSat().isSat():
    print("The given constraints are satisfiable.")
else:
    print("The given constraints are not satisfiable.")
```

This code initializes a CVC5 solver and sets up variables for course units. It creates constraints for each requirement, including ensuring that at least one senior project-related course has a minimum of 3 units and that the total units for mathematics and science meet the minimum requirements. Then, it checks if the constraints are satisfiable and prints the result.