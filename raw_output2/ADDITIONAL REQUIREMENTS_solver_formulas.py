To generate CVC5 formulas in Python that check the constraints specified in the additional requirements for the MSCS degree, we need to break down the requirements and translate them into CVC5 constraints.

Below is the Python code with CVC5 solver formulas for each specified requirement:

1. **All courses must be numbered 100 or greater**: This is inherently satisfied since all course numbers provided are 100 or greater.

2. **At most 10 units of Foundations requirement courses may be counted toward your 45 units**:

3. **At most 3 units of 1-2 unit seminars may be counted toward your 45 units**:

4. **At least 36 units submitted for the MSCS degree, including all courses taken for breadth and depth, must be taken for a letter grade**:

5. **The average grade in the courses submitted for the MSCS must be at least a B (3.0 in Stanford's GPA scale)**:

6. **Units previously applied toward BS requirements may not also be counted toward the MSCS**: This is a bit difficult to encode without knowing which units were previously counted towards the BS.

7. **You must complete at least 45 graduate units at Stanford before receiving the MSCS degree**:

Here is the Python code for these requirements using the CVC5 solver:

```python
import pycvc5
from pycvc5 import Solver
from pycvc5 import Kind

solver = Solver()
solver.setLogic("QF_LIA")

# Declare course unit variables:
course_units = {
    "cs103_units": solver.mkInteger(3),
    "cs109_units": solver.mkInteger(4),
    "stat116_units": solver.mkInteger(3),
    # add remaining unit declarations as per your list...
    "cs229_units": solver.mkInteger(3),
    # Add more units if needed here...
}

# Example: we have a list of the units taken for Foundations Requirement, which should be a subset of the complete list.
foundations_units = [
    course_units["cs103_units"],
    course_units["cs109_units"],
    course_units["cs161_units"],
    course_units["cs107_units"],
    course_units["cs110_units"]
]

# Add the constraint that the total units for the Foundations Requirement must not exceed 10
foundations_total_units = solver.mkInteger(0)
for unit in foundations_units:
    foundations_total_units = solver.mkTerm(Kind.ADD, foundations_total_units, unit)

solver.assertFormula(solver.mkTerm(Kind.LEQ, foundations_total_units, solver.mkInteger(10)))

# Example seminar units, assuming we have a method to determine seminar courses
seminar_units = [
    course_units["some_seminar_units_1"],
    course_units["some_seminar_units_2"]
]

# Add the constraint that the total seminar units must not exceed 3
seminar_total_units = solver.mkInteger(0)
for unit in seminar_units:
    seminar_total_units = solver.mkTerm(Kind.ADD, seminar_total_units, unit)

solver.assertFormula(solver.mkTerm(Kind.LEQ, seminar_total_units, solver.mkInteger(3)))

# Add the constraint for the total units and those taken for a letter grade
total_units = solver.mkInteger(0)
letter_grade_units = solver.mkInteger(0)
for course, unit in course_units.items():
    total_units = solver.mkTerm(Kind.ADD, total_units, unit)
    # Assuming we know which courses are taken for a letter grade:
    if course in ["list_of_letter_grade_courses"]:
        letter_grade_units = solver.mkTerm(Kind.ADD, letter_grade_units, unit)

# Constraint that the total units should be at least 45
solver.assertFormula(solver.mkTerm(Kind.GEQ, total_units, solver.mkInteger(45)))

# Constraint that the letter grade units should be at least 36
solver.assertFormula(solver.mkTerm(Kind.GEQ, letter_grade_units, solver.mkInteger(36)))

# Average grade must be at least B (3.0 in GPA)
# Assuming we have grades as integers and units, we compute the weighted average
grades = {
    "cs103_grade": solver.mkInteger(3),  # Assume A = 4, B = 3, C = 2, etc.
    "cs109_grade": solver.mkInteger(4),
    # add remaining grade declarations as per your list...
    "cs229_grade": solver.mkInteger(3),
}
total_grade_points = solver.mkInteger(0)

for course, grade in grades.items():
    total_grade_points = solver.mkTerm(Kind.ADD, total_grade_points, solver.mkTerm(Kind.MUL, unit, grade))

# The average grade calculation
average_grade = solver.mkTerm(Kind.DIV, total_grade_points, total_units)

# Constraint that the average grade should be at least 3.0
solver.assertFormula(solver.mkTerm(Kind.GEQ, average_grade, solver.mkInteger(3)))

# Check the constraints
result = solver.checkSat()
assert result.isSat(), "The course plan does not satisfy the MSCS degree requirements!"

print("The course plan satisfies all the specified constraints.")
```

In this code:
- We have defined integer variables for units for each course.
- Then, we have set constraints for the Foundations requirement to not exceed 10 units.
- We ensure that at most 3 units of the seminar courses are counted.
- We also ensure the total units are at least 45 and at least 36 units from courses taken for a letter grade.
- Calculated the average grade to ensure it's at least a B (3.0 GPA).

Note: Some assumptions in the code need to be adjusted based on actual data input and lists for letter-graded courses and specific seminars. The example provides a general approach to adding constraints for the MSCS degree requirements.