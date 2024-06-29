Sure, based on the provided text, I will generate CVC5 solver formulas in Python to check if specified constraints in the Engineering Fundamentals section are satisfied. Here's the detailed implementation:

1. Define the logic for the minimum unit requirements.
2. Define the constraints on the core courses.
3. Define the constraints on the elective courses.
4. Generate CVC5 formulas to check if specified constraints are satisfied.

Here's the complete implementation in Python:

```python
from cvc5 import Solver, Kind

# Initialize the solver
solver = Solver()

# Define the courses and their respective units
courses = [
    "MATH19", "MATH20", "MATH21", "CS103", "CS109", "PHYS41", "PHYS43",
    "MATH51", "MATH52", "MATH53", "MATH104", "MATH107", "MATH108", "MATH109", "MATH110", "MATH113",
    "CS205L", "CME100", "CME102", "CME104", "ENGR108", "CS157", "PHIL151"
]

# Define the units for core courses explicitly based on assumed values
course_units = {
    "CS106B": 5,
    "ENGR40M": 3,
    "ENGR76": 3,
    "CS103": 5,
    "CS109": 5,
    "PHYS41": 4,
    "PHYS43": 4,
    "MATH19": 5,
    "MATH20": 5,
    "MATH21": 5,
    "MATH51": 5,
    "MATH52": 5,
    "MATH53": 5,
    "MATH104": 5,
    "MATH107": 5,
    "MATH108": 5,
    "MATH109": 5,
    "MATH110": 5,
    "MATH113": 5,
    "CS205L": 3,
    "CME100": 5,
    "CME102": 5,
    "CME104": 5,
    "ENGR108": 3,
    "CS157": 3,
    "PHIL151": 3
}

# Define constraints for Engineering Fundamentals
engineering_fundamentals_courses = [
    "CS106B",
    ("ENGR40M", "ENGR76")
]

# Sum the units for all courses to meet the minimum requirement
def sum_course_units(selected_courses):
    return sum(course_units[course] for course in selected_courses)

# Create variables for whether each course is taken
course_vars = {course: solver.mkBoolVar(course) for course in courses}

# Assert the Engineering Fundamentals constraints
for course in engineering_fundamentals_courses:
    if isinstance(course, tuple):
        or_term = solver.mkTerm(Kind.OR, [course_vars[c] for c in course])
        solver.assertFormula(or_term)
    else:
        solver.assertFormula(course_vars[course])

# Assert the minimum unit requirements for Engineering Fundamentals
min_units = 10
sum_units = solver.mkReal(0)
for course in engineering_fundamentals_courses:
    if isinstance(course, tuple):
        some_course_taken = solver.mkTerm(Kind.ADD, [solver.mkIte(course_vars[c], solver.mkReal(course_units[c]), solver.mkReal(0)) for c in course])
        sum_units = solver.mkTerm(Kind.ADD, sum_units, some_course_taken)
    else:
        sum_units = solver.mkTerm(Kind.ADD, sum_units, solver.mkIte(course_vars[course], solver.mkReal(course_units[course]), solver.mkReal(0)))
solver.assertFormula(solver.mkTerm(Kind.GEQ, sum_units, solver.mkReal(min_units)))

# Check if the requirements are satisfied
if solver.checkSat().isSat():
    print("The constraints are satisfied.")
else:
    print("The constraints are not satisfied.")
```

This Python code demonstrates the process of configuring the CVC5 solver to enforce constraints based on the course requirements and units specified for the Engineering Fundamentals section. It includes:

- Defining the courses and their units.
- Setting up the constraints based on the course requirements.
- Asserting the minimum unit requirement.
- Checking the constraints with the CVC5 solver.

The provided code should be a good starting point but may require adjustments if exact unit values from specific course data are available.