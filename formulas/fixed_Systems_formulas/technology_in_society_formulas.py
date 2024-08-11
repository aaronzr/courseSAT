
import os
import sys
import cvc5
import json
from cvc5 import Kind

# Initialize the solver with appropriate options
def solver_init(): 
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver 

# Check the satisfiability of the constraints and print relevant information
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

# Function to evaluate the transcript against TiS approved courses
def function(transcript):
    solver = solver_init()
    
    # Define the course variable
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Course constraint from transcript courses taken
    constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint = solver.mkTerm(Kind.OR, *constraints_set)
    
    # List of TiS approved courses
    tis_courses = ['TiS Course 1', 'TiS Course 2', 'TiS Course 3']
    
    # TiS approved course constraints
    approved_courses = [solver.mkString(course) for course in tis_courses]
    constraint_tis = solver.mkTerm(Kind.OR, *[solver.mkTerm(Kind.EQUAL, course_variable, course) for course in approved_courses])

    # AND the course constraint with TiS Approved course constraint
    final_constraint = solver.mkTerm(Kind.AND, constraint, constraint_tis)

    # Assert the final constraint
    solver.assertFormula(final_constraint)

    # Return the result of the check
    return result_checker(solver, [course_variable])

# Simple test case
transcript_example = {
    "Courses_Taken": [
        {"Course_ID": "TiS Course 1"},
        {"Course_ID": "Non-TiS Course 1"},
    ]
}

# Print the transcript and result
print("Transcript:", transcript_example)
result = function(transcript_example)
if result.isSat():
    print("The transcript meets the Technology in Society requirement.")
else:
    print("The transcript does not meet the Technology in Society requirement.")
