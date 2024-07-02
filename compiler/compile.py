import cvc5
from parser import *
from cvc5.pythonic import *

def generate_cvc5_formulas(students, courses, requirements):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")

    # Create Variables
    vars_dict = {}
    for student in students:
        vars_dict[student.student_id] = {}
        for course in student.courses:
            vars_dict[student.student_id][course.course_id] = solver.mkBoolean(course.grade in ['A', 'B', 'C'])

    # Constraints for each student
    for student in students:
        student_vars = vars_dict[student.student_id]
        total_units = solver.mkInteger(0)
        letter_grade_units = solver.mkInteger(0)
        elective_units = solver.mkInteger(0)

        for course in student.courses:
            units_term = solver.mkInteger(course.units)
            total_units = solver.mkTerm(Kind.ADD, total_units, units_term)
            if course.grade in ['A', 'B', 'C']:
                letter_grade_units = solver.mkTerm(Kind.ADD, letter_grade_units, units_term)
            if 1 <= course.units <= 2:
                elective_units = solver.mkTerm(Kind.ADD, elective_units, units_term)

        # Minimum Units Requirement
        solver.assertFormula(solver.mkTerm(Kind.GEQ, total_units, solver.mkInteger(45)))

        # Letter Grade Requirement
        solver.assertFormula(solver.mkTerm(Kind.GEQ, letter_grade_units, solver.mkInteger(36)))

        # Electives Unit Limit
        solver.assertFormula(solver.mkTerm(Kind.LEQ, elective_units, solver.mkInteger(3)))

    return solver


parser = Parser(input_data)
parser.parse()

# Debug: Print students and their courses for verification
for student in parser.students:
    print(f"Student: {student.name}")
for course in parser.courses:
    print(course.title)
# Generate CVC5 Formulas
solver = generate_cvc5_formulas(parser.students, parser.courses, parser.requirements)

# Check Satisfiability
result = solver.checkSat()
print(f"Sat: {result}")
if result.isSat():
    model = solver.getModel()
    print(f"Model: {model}")
else:
    print("No satisfying solution found.")