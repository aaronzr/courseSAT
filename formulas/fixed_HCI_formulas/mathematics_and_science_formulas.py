
import os
import sys
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

# Define the transcript schema template
transcript_schema = {
    "Student": {
        "Name": "John Doe",
        "Program": "Computer Science",
        "StudentID": 12345678,
        "Coterm": False
    },
    "AP_Credits": [
        {"Advanced_Placement": "Mathematics", "Earned_Units": 10}
    ],
    "Courses_Taken": [
        {"Course_ID": 1, "Title": "MATH19", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": 2, "Title": "CS103", "Earned_Units": 5, "Grade": "B"},
        {"Course_ID": 3, "Title": "PHIL151", "Earned_Units": 3, "Grade": "A"}
    ],
    "Deviations": [
        {
            "Deviated_Course_ID": None,
            "Approved": False,
            "Approved_By": None,
        },
        {
            "Deviated_Course_ID": None,
            "Approved": False,
            "Approved_By": None,
        }
    ],
    "Approval": [
        {
            "Approved": False,
            "Approved_By": None,
            "Approved_Course_ID": None
        },
        {
            "Approved": False,
            "Approved_By": None,
            "Approved_Course_ID": None
        }
    ],
    "Cumulative_GPA": {
        "Undergrad": 3.75,
        "Graduate": None,
    },
}

def generate_math_requirement_constraints(solver, transcript):
    # Constraint variables
    course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")

    # Courses taken by the student
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, 
                     solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]

    constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)

    # Math19 (Calculus)
    math19_constraint = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("MATH19"))

    # Math20
    math20_constraint = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("MATH20"))

    # Math21
    math21_constraint = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("MATH21"))

    # CS103 (Mathematical Foundations of Computing)
    cs103_constraint = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS103"))

    # CS109 (Introduction to Probability for Computer Scientists)
    cs109_constraint = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS109"))

    # Math Electives from options
    math_electives = ['MATH51', 'MATH52', 'MATH53', 'MATH104', 'MATH107', 'MATH108', 
                      'MATH109', 'MATH110', 'MATH113', 'CS157', 'CS205L', 'PHIL151', 
                      'CME100', 'CME102', 'CME104', 'ENGR108']

    math_electives_constraints = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(elective)) 
                                  for elective in math_electives]

    # Combine all constraints
    final_constraint = solver.mkTerm(Kind.OR, math19_constraint, math20_constraint, 
                                 math21_constraint, cs103_constraint, cs109_constraint, 
                                 *math_electives_constraints)

    solver.assertFormula(final_constraint)

def function(transcript):
    solver = solver_init()
    generate_math_requirement_constraints(solver, transcript)
    result = result_checker(solver, ["course1"])
    return result

# Test the function with the provided transcript schema
if __name__ == "__main__":
    function(transcript_schema)
