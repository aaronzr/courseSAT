To generate the required CVC5 solver formulas in Python to verify if the course choices meet the specified constraints from the MSCS Program Sheet for the Artificial Intelligence Specialization, we need to follow a systematic approach. Below is the complete Python code using CVC5's Python API which adheres to the required constraints.

Make sure to install the CVC5 Python bindings before running this code. You can install it via pip:
```
pip install cvc5
```

### Python Code with CVC5 Formulas

```python
import cvc5
from cvc5 import Kind

# Initialize the solver
solver = cvc5.Solver()

# Assuming each course is represented as a boolean variable indicating whether it was taken
# Let's initialize variables for each course in the elective list, as well as the required ones

course_vars = {}
elective_courses = [
    'cs111', 'cs140', 'cs140e', 'cs143', 'cs144', 'cs145', 'cs147', 'cs148', 
    'cs149', 'cs151', 'cs155', 'cs161', 'cs173', 'cs181', 'cs182', 'cs190', 
    'cs195', 'cs196', 'cs198', 'cs199', 'cs200', 'cs202', 'cs210b', 'cs221', 
    'cs223a', 'cs224n', 'cs224s', 'cs224u', 'cs224v', 'cs224w', 'cs225a', 
    'cs228', 'cs229', 'cs229m', 'cs230', 'cs231a', 'cs231n', 'cs233', 'cs234', 
    'cs235', 'cs236', 'cs237a', 'cs237b', 'cs238', 'cs239', 'cs242', 'cs243', 
    'cs244', 'cs244b', 'cs245', 'cs246', 'cs247', 'cs248', 'cs248a', 'cs251', 
    'cs255', 'cs257', 'cs258', 'cs261', 'cs262', 'cs263', 'cs264', 'cs265', 
    'cs266', 'cs268', 'cs270', 'cs271', 'cs273a', 'cs273b', 'cs274', 'cs275', 
    'cs276', 'cs278', 'cs279', 'cs281', 'cs295', 'cs302', 'cs322', 'cs324', 
    'cs325b', 'cs326', 'cs327a', 'cs329', 'cs330', 'cs331b', 'cs332', 'cs333', 
    'cs345', 'cs348a', 'cs348b', 'cs348c', 'cs348e', 'cs348i', 'cs348k', 
    'cs348n', 'cs355', 'cs356', 'cs361', 'cs368', 'cs371', 'cs372', 'cs373', 
    'cs375', 'cs377', 'cs379', 'cs398', 'cs399', 'cs428a', 'cs428b', 'cs432', 
    'ee180', 'ee263', 'ee276', 'ee278', 'ee282', 'ee364a', 'ee364b', 'ee377', 
    'ee378b', 'ee382e', 'engr205', 'engr209a', 'msande220', 'msande226', 'msande252', 
    'psych209', 'stats202', 'stats315a', 'stats315b'
]

required_courses = [
    'cs103', 'cs161', ('cs107', 'cs107e'), ('cs110', 'cs111'), 
    ('cs109', 'ee178', 'stat116', 'cme106', 'msande220')
]

# Create a boolean variable for each course
for course in elective_courses:
    course_vars[course] = solver.mkBool(course)

# Sample course choices (this would be the actual input in realistic code)
course_choices = {
    'cs154': [False, 0],
    'cs140': [True, 3],
    'history244f': [True, 3],
    'cs348a': [True, 3]
}

# Let's translate course choices to solver variables
taken_courses = {}
for course, (taken, units) in course_choices.items():
    if course in course_vars:
        taken_courses[course] = (taken, units)

# Assert constraints for the required courses
for req in required_courses:
    if isinstance(req, tuple):
        or_terms = []
        for c in req:
            if c in course_vars:
                or_terms.append(course_vars[c])
        if or_terms:
            solver.assertFormula(solver.mkTerm(Kind.OR, *or_terms))
    else:
        if req in course_vars:
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, course_vars[req], solver.mkTrue()))

# ELECTIVES constraints as per the program sheet
# Condition to count at least 3 units from electives and ensuring no course is CS196, CS198, CS390A/B/C  

elective_constraints = []
elective_units = 0

for course in elective_courses:
    if course in taken_courses:
        taken, units = taken_courses[course]
        if taken:
            elective_constraints.append(course_vars[course])
            elective_units += units
        
assert elective_units >= 3

solver.assertFormula(solver.mkTerm(Kind.OR, *elective_constraints))

# Example to check if we meet the minimum elective units
min_units = 3
unit_constraints = []

for course, (_, units) in taken_courses.items():
    if course in elective_courses and 'cs196' not in course and 'cs198' not in course and not course.startswith('cs390'):
        unit_constraints.append(solver.mkTerm(Kind.GEQ, solver.mkReal(units), solver.mkReal(min_units)))

# Ensuring we meet the unit constraints for electives
if unit_constraints:
    solver.assertFormula(solver.mkTerm(Kind.AND, *unit_constraints))

# Check satisfiability
result = solver.checkSat()
print(result.isSat())
```

### Explanation
1. **Initialize Solver**: We initialize the CVC5 solver.
2. **Declare Variables**: Create boolean variables for all the elective courses.
3. **Parse Course Choices**: Convert provided course choices into solver variables.
4. **Assert Required Courses**: 
    - Loop through the list of required courses and build proper constraints for tuples (indicating alternative courses).
5. **Elective Constraints**:
    - Ensure that elective courses (excluding invalid courses `CS196, CS198, CS390A/B/C`) account for at least 3 units.

### Assumptions
- Variable `course_choices` is provided.
- Units and course specifics match the program sheet constraints.

This should help verify if the current course selections satisfy the elective constraints of the program.

### Note
You need to substitute actual course units and make sure all elective and required courses constraints are met as per updated requirements document. Each input should be carefully checked against the constraints deriving from the program sheet.