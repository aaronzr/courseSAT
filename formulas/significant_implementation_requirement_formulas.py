
import cvc5
import json
from cvc5 import Kind

def solver_init():
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver

def result_checker(solver, variables):
    result = solver.checkSat()
    print("Satisfiability:", result)
    if result.isSat():
        print("SAT")
        if variables:
            for variable in variables:
                model = solver.getValue(variable)
                print(f"Model for {variable}:", model)
    else:
        core = solver.getUnsatCore()
        print("Unsat requirement core is: ", core)
    return result

def check_significant_implementation_requirement(transcript):
    solver = solver_init()

    # List of courses satisfying the Significant Implementation Requirement
    implementation_courses = ['CS 140', 'CS 140E', 'CS 143', 'CS 144', 'CS 145', 'CS 148', 'CS 151', 'CS 190',
                              'CS 210B', 'CS 212', 'CS 221', 'CS 227B', 'CS 231N', 'CS 243', 'CS 248', 'CS 248A', 'CS 341']

    course_var = solver.mkConst(solver.getStringSort(), "course_var")

    # Constraint: At least one of the courses in the transcript satisfies the Significant Implementation Requirement
    implementation_constraint = [
        solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(course.get("Title"))) 
        for course in transcript.get("Courses_Taken", []) 
        if course.get("Title") in implementation_courses
    ]
    if len(implementation_constraint) == 1:
        significant_implementation_constraint = implementation_constraint[0]
    elif implementation_constraint:
        significant_implementation_constraint = solver.mkTerm(Kind.OR, *implementation_constraint)
    else:
        significant_implementation_constraint = solver.mkFalse()

    # Constraint: The course must be taken for a letter grade at Stanford
    grade_constraint = [
        solver.mkTerm(
            Kind.AND,
            solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString("A")),
            solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(course.get("Title")))
        )
        for course in transcript.get("Courses_Taken", [])
        if course.get("Title") in implementation_courses
    ]
    if len(grade_constraint) == 1:
        letter_grade_constraint = grade_constraint[0]
    elif grade_constraint:
        letter_grade_constraint = solver.mkTerm(Kind.OR, *grade_constraint)
    else:
        letter_grade_constraint = solver.mkFalse()

    taken_at_stanford = solver.mkTrue()  # Assuming all courses are taken at Stanford by default as per input

    coterm_var = solver.mkConst(solver.getBooleanSort(), "coterm_var")
    coterm_constraint = solver.mkTerm(Kind.IMPLIES, coterm_var, solver.mkTerm(
        Kind.LEQ,
        solver.mkInteger(len([course.get("Title") for course in transcript.get("Courses_Taken", []) if course.get("Title") in implementation_courses])),
        solver.mkInteger(2)))

    deviation_approved_by_cynthia = [
        solver.mkTerm(
            Kind.AND,
            solver.mkTerm(Kind.EQUAL, solver.mkString(deviation.get("Approved_By")), solver.mkString("Cynthia Lee")),
            solver.mkTerm(Kind.EQUAL, solver.mkBoolean(deviation.get("Approved")), solver.mkTrue())
        )
        for deviation in transcript.get("Deviations", [])
    ]
    if len(deviation_approved_by_cynthia) == 1:
        deviation_constraint = deviation_approved_by_cynthia[0]
    elif deviation_approved_by_cynthia:
        deviation_constraint = solver.mkTerm(Kind.OR, *deviation_approved_by_cynthia)
    else:
        deviation_constraint = solver.mkFalse()

    final_constraints = solver.mkTerm(Kind.AND, significant_implementation_constraint, letter_grade_constraint, 
                                      taken_at_stanford, coterm_constraint, deviation_constraint)

    # Assert the final constraints
    solver.assertFormula(final_constraints)

    # Check satisfiability
    result = result_checker(solver, [course_var, coterm_var])
    return result

# Example transcript
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "MS in CS",
        "StudentID": 123456,
        "Coterm": True
    },
    "AP_Credits": [],
    "Courses_Taken": [
        {"Course_ID": 1, "Title": "CS 140", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": 2, "Title": "CS 221", "Earned_Units": 3, "Grade": "A"}
    ],
    "Deviations": [
        {"Deviated_Course_ID": "None", "Approved": False, "Approved_By": "None"}
    ],
    "Approval": [
        {"Approved": True, "Approved_By": "Cynthia Lee", "Approved_Course_ID": "CS 221"}
    ],
    "Cumulative_GPA": {
        "Undergrad": 3.8,
        "Graduate": 3.9
    }
}

result = check_significant_implementation_requirement(transcript)
print("Satisfiable: ", result)
