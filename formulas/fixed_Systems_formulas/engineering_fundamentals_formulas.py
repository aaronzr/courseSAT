
import z3

# Ensure solver is instantiated
solver = z3.Solver()  # Replace with correct initialization of your solver if needed

# Define a real variable for the course grade constraint
course_variable_real = z3.Real('course_variable_real')  # Define your course_variable_real appropriately

# Assuming transcript and tis_course are defined somewhere in your code
transcript = {
    "Courses_Taken": [
        {"Course_ID": "ENG101", "Course_Grade": 3.5},
        # Other courses can be added here...
    ]
}

tis_course = "ENG101"

# Fixing the original line with proper context
course_grade = next((course.get("Course_Grade") for course in transcript["Courses_Taken"] if course.get("Course_ID") == tis_course), None)
if course_grade is not None:
    # Ensuring course grade is a float and then making the constraint
    tis_gpa_constraint = course_variable_real >= course_grade
    solver.add(tis_gpa_constraint)
else:
    raise ValueError(f"Course ID {tis_course} not found in the transcript")

# Solver can then be used to check for satisfiability or further processing
if solver.check() == z3.sat:
    m = solver.model()
    print("Satisfiable, example model:", m)
else:
    print("Not satisfiable")
