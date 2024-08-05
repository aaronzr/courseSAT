
import os
import sys
import cvc5
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
    course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
    course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")

    # Constraints for courses taken
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)
    constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)

    # Define course IDs for required math courses
    math19 = 'MATH19'
    math20 = 'MATH20'
    math21 = 'MATH21'
    cs103 = 'CS103'
    cs109 = 'CS109'

    # Constraints for required math courses
    course_ids_math = [math19, math20, math21, cs103, cs109]
    constraints_set3 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course_id)) for course_id in course_ids_math]
    constraints_set4 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course_id)) for course_id in course_ids_math]
    constraint_3 = solver.mkTerm(Kind.OR, *constraints_set3)
    constraint_4 = solver.mkTerm(Kind.OR, *constraints_set4)

    # Combine all constraints
    constraint_5 = solver.mkTerm(Kind.AND, constraint_1, constraint_2, constraint_3, constraint_4)

    # Final formula
    solver.assertFormula(constraint_5)

    # Check result
    variables = [course_variable_1, course_variable_2]
    return result_checker(solver, variables)

# Simple test case
def main():
    transcript = {
        "Courses_Taken": [
            {"Course_ID": "MATH19"},
            {"Course_ID": "CS109"}
        ]
    }
    function(transcript)

if __name__ == "__main__":
    main()
