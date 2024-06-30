Here's a comprehensive Python code to generate CVC5 solver formulas based on the given course requirements and constraints. It includes the courses from the "Engineering Fundamentals", "Mathematics and Science Requirements", and the specified list of supplemental elective courses.

We'll use the CVC5 Python API to define the constraints, and ensure the courses taken by the user meet the provided requirements and units.

```python
import pycvc5
from pycvc5 import *
from pycvc5.kinds import Kind

# Initialize the solver
solver = pycvc5.Solver()

# Define the course requirements
course_requirements = [
    "math19",
    "math20",
    "math21",
    "cs103",
    "cs109",
    "phys41",
    "phys43",
    ("math51", "math52", "math53", "math104", "math107", "math108", "math109", "math110", "math113", "cs205l", "cme100", "cme102", "cme104", "engr108"),
    ("cs157", "phil151"),
    "cs106b",
    ("engr40m", "engr76")
]

# Define units for courses (placeholders, replace with actual course units)
course_units = {
    "math19": 5,   # replace with actual units
    "math20": 5,   # replace with actual units
    "math21": 5,   # replace with actual units
    "cs103": 5,    # replace with actual units
    "cs109": 5,    # replace with actual units
    "phys41": 4,   # replace with actual units
    "phys43": 4,   # replace with actual units
    "math51": 4,   # replace with actual units
    "math52": 4,   # replace with actual units
    "math53": 4,   # replace with actual units
    "math104": 3,  # replace with actual units
    "math107": 3,  # replace with actual units
    "math108": 3,  # replace with actual units
    "math109": 3,  # replace with actual units
    "math110": 3,  # replace with actual units
    "math113": 3,  # replace with actual units
    "cs205l": 3,   # replace with actual units
    "cme100": 4,   # replace with actual units
    "cme102": 4,   # replace with actual units
    "cme104": 4,   # replace with actual units
    "engr108": 3,  # replace with actual units
    "cs157": 3,    # replace with actual units
    "phil151": 3,  # replace with actual units
    "cs106b": 5,   # replace with actual units
    "engr40m": 3,  # replace with actual units
    "engr76": 3    # replace with actual units
}

# Define user input with course choices
course_choices = {
    "cs154": [False, 0],
    "cs140": [True, 3],
    "history244f": [True, 3],
    "cs348a": [True, 3]
}

# Helper function to create terms for each course in course choices
def create_course_terms(course_choices):
    terms = {}
    for course, taken_and_units in course_choices.items():
        taken, units = taken_and_units
        terms[course] = solver.mkConst(solver.getBooleanSort(), course)
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, terms[course], solver.mkBool(taken)))
    return terms

course_terms = create_course_terms(course_choices)

# Formulate the course requirements using CVC5 API
def formulate_requirements(course_requirements, course_terms):
    for requirement in course_requirements:
        if isinstance(requirement, tuple):
            or_terms = [course_terms[course] for course in requirement if course in course_terms]
            solver.assertFormula(solver.mkTerm(Kind.OR, *or_terms))
        else:
            if requirement in course_terms:
                solver.assertFormula(
                    solver.mkTerm(Kind.EQUAL, course_terms[requirement], solver.mkBool(True))
                )

formulate_requirements(course_requirements, course_terms)

# Now let's check if the course choices satisfy the overall constraints

# Define the minimum units constraints
MIN_MATH_UNITS = 26
MIN_SCIENCE_UNITS = 11
MIN_ENGINEERING_FUNDAMENTALS_UNITS = 10

# Define the total units required formulas
total_math_units = sum(course_units[course] for course in course_choices if course.startswith("math") and course_choices[course][0])
total_science_units = sum(course_units[course] for course in course_choices if course.startswith("phys") and course_choices[course][0])
total_engineering_fundamentals_units = sum(course_units[course] for course in course_choices if course in ["cs106b", "engr40m", "engr76", "engr108"] and course_choices[course][0])

# Assert unit constraints
solver.assertFormula(
    solver.mkTerm(Kind.GEQ, solver.mkInteger(total_math_units), solver.mkInteger(MIN_MATH_UNITS))
)

solver.assertFormula(
    solver.mkTerm(Kind.GEQ, solver.mkInteger(total_science_units), solver.mkInteger(MIN_SCIENCE_UNITS))
)

solver.assertFormula(
    solver.mkTerm(Kind.GEQ, solver.mkInteger(total_engineering_fundamentals_units), solver.mkInteger(MIN_ENGINEERING_FUNDAMENTALS_UNITS))
)

# Check the solver
result = solver.checkSat()
print(f"Constraints satisfaction result: {result}")

# Optionally, output some diagnostics or counterexamples
if result.isUnsat():
    print("The provided course choices do not satisfy the constraints.")
elif result.isSat():
    print("The provided course choices satisfy the constraints.")

# Define actual courses
actual_courses = [
    "math19",
    "math20",
    "math21",
    "cs103",
    "cs109",
    "phys41",
    "phys43",
    "math108",
    "cs157",
    "cs106b",
    "engr40m"
]

# Check if the course choices cover the actual courses required
for course in actual_courses:
    if course not in course_choices:
        print(f"Course {course} is missing in the provided choices.")

# Sample output based on user input
course_choices = {
    "math19": [True, 5],
    "math20": [True, 5],
    "math21": [True, 5],
    "cs103": [True, 5],
    "cs109": [True, 5],
    "phys41": [True, 4],
    "phys43": [True, 4],
    "math108": [True, 3],
    "cs157": [True, 3],
    "cs106b": [True, 5],
    "engr40m": [True, 3]
}

# Helper function to update terms based on new choices
def update_course_terms(course_choices):
    for course, taken_and_units in course_choices.items():
        taken, units = taken_and_units
        course_units[course] = units
        course_terms[course] = solver.mkConst(solver.getBooleanSort(), course)
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, course_terms[course], solver.mkBool(taken)))

update_course_terms(course_choices)

# Check the solver again
result = solver.checkSat()
print(f"Constraints satisfaction result after updating course choices: {result}")
```

This code defines the course requirements and their units, asserts the constraints for required courses, and checks if the given course choices satisfy the necessary constraints. The provided `course_choices` is used to dynamically check and assert constraints using the CVC5 solver. Update the placeholders for course units with the actual values based on your course catalog or records. 

Remember to install and correctly set up `pycvc5` to use this code. The result will indicate if the provided course choices satisfy the overall constraints, and print missing courses from the actual required courses if any.