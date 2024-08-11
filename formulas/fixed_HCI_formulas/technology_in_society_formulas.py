
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
    
    # Define approved TiS courses and the year taken
    approved_courses = ['TiS 101', 'TiS 102', 'TiS 103']
    year_taken = 2023

    # Create variables for course and year
    course_variable = solver.mkConst(solver.getStringSort(), "course")
    year_variable = solver.mkConst(solver.getIntegerSort(), "year")

    # Course is in transcript.courses_taken
    course_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Title"))) 
                          for course in transcript.get("Courses_Taken", [])]

    # Year taken is the specified year
    year_constraint = solver.mkTerm(Kind.EQUAL, year_variable, solver.mkInteger(year_taken))

    # Course is in the approved TiS courses list
    approved_course_constraint = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(approved_course)) 
                                  for approved_course in approved_courses]
    approved_course_constraint = solver.mkTerm(Kind.OR, *approved_course_constraint)

    # Combine all constraints
    final_constraint = solver.mkTerm(Kind.AND, year_constraint, approved_course_constraint, 
                                      *course_constraints)

    # Assert the final constraint
    solver.assertFormula(final_constraint)

    return result_checker(solver, [course_variable, year_variable])

# Example test case
if __name__ == "__main__":
    transcript_example = {
        "Courses_Taken": [
            {"Title": "TiS 101", "Year": 2023},
            {"Title": "Math 101", "Year": 2022},
            {"Title": "Science 102", "Year": 2023}
        ]
    }

    function(transcript_example)
