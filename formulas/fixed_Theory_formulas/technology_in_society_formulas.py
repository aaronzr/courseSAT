
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

# Function to generate constraints for the TiS Requirement
def generate_TiS_constraint(transcript, solver, TiS_Approved_courses):
    # Get all TiS Approved courses from the transcript
    TiS_courses = [course.get("Course_ID") for course in transcript.get("Courses_Taken", []) if course.get("Title") in TiS_Approved_courses]
    TiS_course_variable = solver.mkConst(solver.getStringSort(), "TiS_course")
    
    # Each TiS course should be taken only once
    individual_constraints = [solver.mkTerm(Kind.EQUAL, TiS_course_variable, solver.mkString(course_id)) for course_id in TiS_courses]
    constraint_1 = solver.mkTerm(Kind.OR, *individual_constraints)
    
    # The TiS course should be taken for a letter grade
    grade_constraints = [solver.mkTerm(Kind.EQUAL, TiS_course_variable, solver.mkString(course_id)) for course_id in TiS_courses]
    constraint_2 = solver.mkTerm(Kind.OR, *grade_constraints)
    
    # Combine all constraints
    final_constraint = solver.mkTerm(Kind.AND, constraint_1, constraint_2)
    
    # Assert the formula
    solver.assertFormula(final_constraint)

# Function to generate constraints for the WiM Requirement
def generate_WiM_constraint(transcript, solver):
    WiM_courses = ["CS 181W", "CS 182W", "CS 191W", "CS 194W", "CS 210B"]
    WiM_course_variable = solver.mkConst(solver.getStringSort(), "WiM_course")
    
    # Check if any of the WiM courses are taken
    WiM_constraints = [solver.mkTerm(Kind.EQUAL, WiM_course_variable, solver.mkString(course_id)) for course_id in WiM_courses]
    constraint_1 = solver.mkTerm(Kind.OR, *WiM_constraints)
    
    # The WiM course should be taken for a letter grade
    grade_constraints = [solver.mkTerm(Kind.EQUAL, WiM_course_variable, solver.mkString(course_id)) for course_id in WiM_courses]
    constraint_2 = solver.mkTerm(Kind.OR, *grade_constraints)
    
    # Combine all constraints
    final_constraint = solver.mkTerm(Kind.AND, constraint_1, constraint_2)
    
    # Assert the formula
    solver.assertFormula(final_constraint)

# Main function to put everything together
def function(transcript):
    solver = solver_init()
    
    # List of TiS Approved courses
    TiS_Approved_courses = ["Course_A", "Course_B", "Course_C"]
    
    # Generate constraints for TiS Requirement
    generate_TiS_constraint(transcript, solver, TiS_Approved_courses)
    
    # Generate constraints for WiM Requirement
    generate_WiM_constraint(transcript, solver)
    
    # Check the result
    result_checker(solver, variables=[])

# Example test case
transcript = {
    "Courses_Taken": [
        {"Course_ID": "001", "Title": "Course_A", "Grade": "A"},
        {"Course_ID": "002", "Title": "CS 182W", "Grade": "B"},
        {"Course_ID": "003", "Title": "Course_B", "Grade": "C"}
    ]
}

# Call the function with the test case
function(transcript)
