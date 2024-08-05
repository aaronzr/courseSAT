
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

    course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
    course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")

    # Course1 is in transcript[*].course; 
    # Course2 is in transcript[*].course;
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)
    constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)

    # CS107 or 107E
    constraints_set3 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS107"))]
    constraints_set4 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString("CS107E"))]
    constraint_3 = solver.mkTerm(Kind.OR, *constraints_set3, *constraints_set4)

    # AND all previous constraints
    constraint_5 = solver.mkTerm(Kind.AND, constraint_1, constraint_2, constraint_3)

    # The same course cannot be used to satisfy two different requirements:
    constraint_6 = solver.mkTerm(Kind.EQUAL, course_variable_1, course_variable_2)
    constraint_7 = solver.mkTerm(Kind.NOT, constraint_6)

    # Final formula
    formula = solver.mkTerm(Kind.AND, constraint_7, constraint_5)

    solver.assertFormula(formula)

    result_checker(solver, [course_variable_1, course_variable_2])

# Example transcript to test the code
transcript = {
    "Courses_Taken": [
        {"Course_ID": "CS107"},
        {"Course_ID": "CS111"},
        {"Course_ID": "CS161"},
        {"Course_ID": "CS221"},
        {"Course_ID": "CS210B"}
    ]
}

# Call the function with the test transcript
function(transcript)
