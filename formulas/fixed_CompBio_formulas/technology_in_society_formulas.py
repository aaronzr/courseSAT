
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
    
    # Create a course variable
    course_variable = solver.mkConst(solver.getStringSort(), "course")
    
    # Extract the courses taken from the transcript
    courses_taken = transcript.get("Courses_Taken", [])
    
    # Create constraints for each course taken
    constraints_set = [
        solver.mkTerm(cvc5.Kind.EQUAL, course_variable, solver.mkString(course.get("Title")))
        for course in courses_taken
    ]
    
    # Course must be on the SoE-approved list the year it is taken
    approved_courses = ["CS 181W", "CS 182W"]  # List of approved TiS courses
    approved_constraints = [
        solver.mkTerm(cvc5.Kind.EQUAL, course_variable, solver.mkString(approved_course))
        for approved_course in approved_courses
    ]
    
    # Combine all constraints
    course_constraint = solver.mkTerm(cvc5.Kind.OR, *constraints_set)
    approved_constraint = solver.mkTerm(cvc5.Kind.OR, *approved_constraints)
    
    # Final formula: Course must be taken and on the approved list
    formula = solver.mkTerm(cvc5.Kind.AND, course_constraint, approved_constraint)
    solver.assertFormula(formula)
    
    return result_checker(solver, [course_variable])

# Example usage of the function and testing
if __name__ == "__main__":
    transcript = {
        "Student": {
            "Name": "John Doe",
            "Program": "BSCS",
            "StudentID": 12345,
            "Coterm": False
        },
        "Courses_Taken": [
            {"Course_ID": 1, "Title": "CS 181W", "Earned_Units": 5, "Grade": "A"},
            {"Course_ID": 2, "Title": "CS 182W", "Earned_Units": 5, "Grade": "B"}
        ]
    }

    function(transcript)
