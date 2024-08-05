
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

def generate_TiS_constraint_formula(solver, transcript):
    course_variable = solver.mkConst(solver.getStringSort(), "course")
    
    # Course is in the transcript
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)
    
    # Course is in the Approved TiS list
    approved_TiS_courses = ['Course1', 'Course2', 'Course3']  # List of approved TiS courses
    constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course_unit)) for course_unit in approved_TiS_courses]
    constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)
    
    # AND all previous individual constraints
    final_constraint = solver.mkTerm(Kind.AND, constraint_1, constraint_2)
    
    solver.assertFormula(final_constraint)

def function(transcript):
    solver = solver_init()
    
    # Generate constraints for the Technology in Society requirement
    generate_TiS_constraint_formula(solver, transcript)
    
    # Check and print the result
    result_checker(solver, [])

# Example transcript for testing
transcript = {
    "Courses_Taken": [
        {"Course_ID": "Course1", "Title": "Course Title 1", "Earned_Units": 4, "Grade": "A"},
        {"Course_ID": "Course2", "Title": "Course Title 2", "Earned_Units": 3, "Grade": "B"},
    ]
}

# Test the function with the example transcript
function(transcript)
