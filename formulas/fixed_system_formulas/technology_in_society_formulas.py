
# Add your imports
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
    # Initialize solver
    solver = solver_init()
    
    # Create course variables
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Ensure course is in the transcript
    course_constraints = []
    for course in transcript.get("Courses_Taken", []):
        cs_term = solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID")))
        course_constraints.append(cs_term)

    course_constraint = solver.mkTerm(Kind.OR, *course_constraints) if course_constraints else solver.mkFalse()

    # Ensure course is in the TiS Approved list
    approved_courses = ['Course1', 'Course2', 'Course3']
    course_in_approved_list = []
    for course in approved_courses:
        ac_term = solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course))
        course_in_approved_list.append(ac_term)

    approved_constraint = solver.mkTerm(Kind.OR, *course_in_approved_list)

    # AND all constraints
    final_constraint = solver.mkTerm(Kind.AND, course_constraint, approved_constraint)

    # Check if the formula is satisfiable
    solver.assertFormula(final_constraint)
    return result_checker(solver, [course_variable])

# Test code correctness
if __name__ == "__main__":
    # Example transcript data
    transcript = {
        "Courses_Taken": [
            {"Course_ID": "Course1"},
            {"Course_ID": "CourseA"}
        ]
    }

    result = function(transcript)
    print("Result of the test case:", result)
