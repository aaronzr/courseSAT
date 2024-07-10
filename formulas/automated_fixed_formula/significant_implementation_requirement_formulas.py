
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

def function(transcript):
    solver = solver_init()

    # Define the course list that satisfies the significant implementation requirement
    significant_implementation_courses = ['CS 140', 'CS 140E', 'CS 143', 'CS 144', 'CS 145', 'CS 148', 'CS 151', 
                                          'CS 190', 'CS 210B', 'CS 212', 'CS 221', 'CS 227B', 'CS 231N', 
                                          'CS 243', 'CS 248 / 248A', 'CS 341']

    # Define the variables for the solver
    course_variable = solver.mkConst(solver.getStringSort(), "course")
    grade_variable = solver.mkConst(solver.getStringSort(), "grade")
    stanford_variable = solver.mkConst(solver.getBooleanSort(), "stanford")

    # Constraint: course in significant_implementation_courses
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course)) for course in significant_implementation_courses]
    constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)

    # Constraint: course taken for a letter grade ('A', 'B', 'C', 'D', 'F')
    letter_grades = ['A', 'B', 'C', 'D', 'F']
    constraints_set2 = [solver.mkTerm(Kind.EQUAL, grade_variable, solver.mkString(grade)) for grade in letter_grades]
    constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)

    # Constraint: course taken at Stanford
    constraint_3 = solver.mkTerm(Kind.EQUAL, stanford_variable, solver.mkBoolean(True))

    # Combining the constraints
    general_constraints = solver.mkTerm(Kind.AND, constraint_1, constraint_2, constraint_3)

    # Check the transcript for the constraints
    transcript_constraints = []
    for course in transcript.get("Courses_Taken", []):
        course_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course["Course_ID"]))]
        course_constraints.append(solver.mkTerm(Kind.EQUAL, grade_variable, solver.mkString(course["Grade"])))
        course_constraints.append(solver.mkTerm(Kind.EQUAL, stanford_variable, solver.mkBoolean(course.get("Taken_At_Stanford", False))))

        transcript_constraints.append(solver.mkTerm(Kind.AND, *course_constraints))

    significant_course_constraint = solver.mkTerm(Kind.OR, *transcript_constraints)
    final_constraint = solver.mkTerm(Kind.AND, general_constraints, significant_course_constraint)

    # Handling coterm students who took equivalent courses as undergraduates
    if transcript["Student"]["Coterm"]:
        undergrad_credits_constraints = []
        for course in transcript.get("Courses_Taken", []):
            if any(sub in course["Title"] for sub in significant_implementation_courses):
                undergrad_credits_constraints.append(solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course["Course_ID"])))

        undergrad_credits_constraint = solver.mkTerm(Kind.OR, *undergrad_credits_constraints)
        final_constraint = solver.mkTerm(Kind.OR, final_constraint, undergrad_credits_constraint)

    # Handling approved deviations
    deviation_constraints = []
    for deviation in transcript.get("Deviations", []):
        if deviation["Approved"]:
            is_approved_by_cynthia = solver.mkTerm(Kind.EQUAL, solver.mkString(deviation["Approved_By"]), solver.mkString("Cynthia Lee"))
            deviation_constraints.append(is_approved_by_cynthia)

    if deviation_constraints:
        deviation_constraint = solver.mkTerm(Kind.AND, *deviation_constraints)
        final_constraint = solver.mkTerm(Kind.OR, final_constraint, deviation_constraint)

    solver.assertFormula(final_constraint)

    # Check satisfiability
    result_checker(solver, [course_variable, grade_variable, stanford_variable])
    return solver

# Example usage for testing
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "MS",
        "StudentID": 123456,
        "Coterm": False
    },
    "Courses_Taken": [
        {"Course_ID": "CS 140", "Title": "Operating Systems", "Earned_Units": 3, "Grade": "A", "Taken_At_Stanford": True},
        {"Course_ID": "CS 145", "Title": "Data Management", "Earned_Units": 3, "Grade": "B", "Taken_At_Stanford": True}
    ],
    "Deviations": [
        {
            "Deviated_Course_ID": "None", 
            "Approved": False,
            "Approved_By": "None"
        }
    ],
    "Approval": [
        {
            "Approved": False,
            "Approved_By": "None",
            "Approved_Course_ID": "None"
        }
    ],
    "Cumulative_GPA": {
        "Undergrad": 3.5,
        "Graduate": 3.7,
    }
}

solver = function(transcript)
