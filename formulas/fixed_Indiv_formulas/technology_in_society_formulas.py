
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

    # Define course variables
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Get the courses taken from the transcript
    courses_taken = transcript.get("Courses_Taken", [])
    
    # Create constraints for courses taken
    constraints_set = [
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID")))
        for course in courses_taken
    ]

    # Define the approved TiS courses
    approved_tis_courses = ["TiS_Course_1", "TiS_Course_2", "TiS_Course_3"]  # Example courses from Approved TiS list

    # Create constraints for TiS courses taken
    constraints_tis = [
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(tis_course))
        for tis_course in approved_tis_courses
    ]

    # Define the constraint for taking 1 course from the Approved TiS list
    constraint_tis = solver.mkTerm(Kind.OR, *constraints_tis)

    # Combine all constraints
    all_constraints = solver.mkTerm(Kind.AND, *constraints_set)

    # Final formula
    formula = solver.mkTerm(Kind.AND, all_constraints, constraint_tis)

    # Assert the formula
    solver.assertFormula(formula)

    # Check and print the result
    result_checker(solver, [course_variable])


# Test case for the function
test_transcript = {
    "Courses_Taken": [
        {"Course_ID": "TiS_Course_1"},
        {"Course_ID": "Math_101"},
        {"Course_ID": "CS_101"}
    ]
}

function(test_transcript)
