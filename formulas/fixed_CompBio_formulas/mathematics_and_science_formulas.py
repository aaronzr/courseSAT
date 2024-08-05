
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

    # Define course variables for Mathematics requirement
    math19 = solver.mkConst(solver.getStringSort(), "MATH19")
    calculus = solver.mkConst(solver.getStringSort(), "Calculus")
    math20 = solver.mkConst(solver.getStringSort(), "MATH20")
    math21 = solver.mkConst(solver.getStringSort(), "MATH21")
    cs103 = solver.mkConst(solver.getStringSort(), "CS103")

    # Course constraints
    constraints_math19 = [solver.mkTerm(Kind.EQUAL, math19, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_calculus = [solver.mkTerm(Kind.EQUAL, calculus, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_math20 = [solver.mkTerm(Kind.EQUAL, math20, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_math21 = [solver.mkTerm(Kind.EQUAL, math21, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_cs103 = [solver.mkTerm(Kind.EQUAL, cs103, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    # Combine all the constraints for Mathematics requirement
    combined_constraints_math19 = solver.mkTerm(Kind.OR, *constraints_math19)
    combined_constraints_calculus = solver.mkTerm(Kind.OR, *constraints_calculus)
    combined_constraints_math20 = solver.mkTerm(Kind.OR, *constraints_math20)
    combined_constraints_math21 = solver.mkTerm(Kind.OR, *constraints_math21)
    combined_constraints_cs103 = solver.mkTerm(Kind.OR, *constraints_cs103)

    # Combine all course constraints into a single constraint
    constraints_mathematics = solver.mkTerm(
        Kind.AND,
        combined_constraints_math19,
        combined_constraints_calculus,
        combined_constraints_math20,
        combined_constraints_math21,
        combined_constraints_cs103
    )

    # Add the constraints to the solver
    solver.assertFormula(constraints_mathematics)

    # Return result for checking
    return result_checker(solver, [math19, calculus, math20, math21, cs103])

# Sample transcript to test code correctness
test_transcript = {
    "Courses_Taken": [
        {"Course_ID": "MATH19"},
        {"Course_ID": "Calculus"},
        {"Course_ID": "MATH20"},
        {"Course_ID": "MATH21"},
        {"Course_ID": "CS103"}
    ]
}

# Test the function with the sample transcript
function(test_transcript)
