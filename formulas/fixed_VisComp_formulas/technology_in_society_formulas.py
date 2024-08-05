
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

    # Course variables
    course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
    course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")

    # Constraints for courses taken
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)
    constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)

    # Constraints for specific courses in the requirement
    constraints_set3 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS 100")), solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS 101")), solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS 102"))]
    constraints_set4 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString("CS 101")), solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString("CS 102")), solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString("CS 103"))]

    constraint_3 = solver.mkTerm(Kind.OR, *constraints_set3)
    constraint_4 = solver.mkTerm(Kind.OR, *constraints_set4)

    # Combine all constraints
    constraint_5 = solver.mkTerm(Kind.AND, constraint_1, constraint_2, constraint_3, constraint_4)

    # Check that the same course is not used to satisfy two different requirements
    constraint_6 = solver.mkTerm(Kind.EQUAL, course_variable_1, course_variable_2)
    constraint_7 = solver.mkTerm(Kind.NOT, constraint_6)

    # Final formula
    formula = solver.mkTerm(Kind.AND, constraint_7, constraint_5)

    # Assert the formula
    solver.assertFormula(formula)

    # Check the result
    result_checker(solver, [course_variable_1, course_variable_2])

# Test case
if __name__ == "__main__":
    # Example transcript
    test_transcript = {
        "Courses_Taken": [
            {"Course_ID": "CS 100"},
            {"Course_ID": "CS 101"},
            {"Course_ID": "CS 102"}
        ]
    }
    function(test_transcript)
