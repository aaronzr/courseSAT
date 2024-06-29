To generate CVC5 solver formulas in Python that check if specified constraints for the Mathematics and Science Requirements are satisfied, we need to define the courses and their unit values as well as the conditions from the requirements document. Here's the code accordingly:

```python
from cvc5 import Solver, Kind

# Initialize solver
solver = Solver()

# Define courses and their unit values
courses_units = {
    "math19": 5,
    "math20": 5,
    "math21": 5,
    "cs103": 5,
    "cs109": 5,
    "phys41": 4,
    "phys43": 4,
    "math51": 5,
    "math52": 5,
    "math53": 5,
    "math104": 3,
    "math107": 3,
    "math108": 3,
    "math109": 3,
    "math110": 3,
    "math113": 3,
    "cs157": 3,
    "cs205l": 3,
    "phil151": 4,
    "cme100": 5,
    "cme102": 5,
    "cme104": 5,
    "engr108": 3,
    "psych30": 4
}

# Define required courses
required_courses = [
    "math19", "math20", "math21",
    "cs103", "cs109",
    "phys41", "phys43"
]

# Define elective groups
math_electives = ["math51", "math52", "math53", "math104", "math107", "math108", "math109", "math110", "math113", "cs205l", "cme100", "cme102", "cme104", "engr108"]
science_electives = ["psych30"]

# Restrictions for electives
math_restriction_1 = ["cs157", "phil151"]

# Total unit constraints
math_units_min = 26
science_units_min = 11
combined_units_min = 37

# Initialize variables
vars = {}
for course in courses_units:
    vars[course] = solver.mkConst(solver.getBooleanSort(), course)

# Formulas for required courses
for course in required_courses:
    solver.assertFormula(solver.mkTerm(Kind.EQUAL, vars[course], solver.mkTrue()))

# Formulas for math electives
electives_chosen = []
for elective in math_electives:
    electives_chosen.append(vars[elective])

# Ensuring at least 2 math electives are chosen
solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkTerm(Kind.ADD, *electives_chosen), solver.mkInteger(2)))

# Restriction: CS. 157 + Phil 151 may not be used in combination
solver.assertFormula(
    solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.AND, vars["cs157"], vars["phil151"]))
)

# Unit constraints for Math, Science, Combined
total_math_units = solver.mkReal(0)
for course in required_courses[:5]:  # First 5 are Math courses
    total_math_units = solver.mkTerm(Kind.ADD, total_math_units, solver.mkTerm(Kind.ITE, vars[course], solver.mkReal(courses_units[course]), solver.mkReal(0)))

for elective in math_electives:
    total_math_units = solver.mkTerm(Kind.ADD, total_math_units, solver.mkTerm(Kind.ITE, vars[elective], solver.mkReal(courses_units[elective]), solver.mkReal(0)))

solver.assertFormula(solver.mkTerm(Kind.GEQ, total_math_units, solver.mkReal(math_units_min)))

total_science_units = solver.mkReal(0)
for course in required_courses[5:]:  # Last 2 are Science courses
    total_science_units = solver.mkTerm(Kind.ADD, total_science_units, solver.mkTerm(Kind.ITE, vars[course], solver.mkReal(courses_units[course]), solver.mkReal(0)))

for elective in science_electives:
    total_science_units = solver.mkTerm(Kind.ADD, total_science_units, solver.mkTerm(Kind.ITE, vars[elective], solver.mkReal(courses_units[elective]), solver.mkReal(0)))

solver.assertFormula(solver.mkTerm(Kind.GEQ, total_science_units, solver.mkReal(science_units_min)))

combined_units = solver.mkTerm(Kind.ADD, total_math_units, total_science_units)
solver.assertFormula(solver.mkTerm(Kind.GEQ, combined_units, solver.mkReal(combined_units_min)))

# Solve the constraints
result = solver.checkSat()
print(result)

if result.isSat():
    print("There exists a valid selection of courses meeting the constraints.")
else:
    print("No valid selection of courses can satisfy the given constraints.")
```

This script initializes a CVC5 solver, sets up the necessary course constraints, and adds the relevant checks for unit totals and elective requirements. This will determine if there exists a valid selection of courses that meets the specified constraints. Note that this is a basic setup. Depending on the full range of course options and constraints, additional adjustments might be necessary.