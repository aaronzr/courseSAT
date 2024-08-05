
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
    
    # 1. CS106B Programming Abstractions:
    course_variable_CS106B = solver.mkConst(solver.getStringSort(), "CS106B")
    # CS106B is \in transcript[*].Course_ID
    constraints_CS106B = [solver.mkTerm(Kind.EQUAL, course_variable_CS106B, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    if constraints_CS106B:
        constraint_CS106B = solver.mkTerm(Kind.OR, *constraints_CS106B) if len(constraints_CS106B) > 1 else constraints_CS106B[0]
    
    # CS106B is in CS106B
    constraints_CS106B_set = [solver.mkTerm(Kind.EQUAL, course_variable_CS106B, solver.mkString("CS106B"))]
    constraint_CS106B_set = constraints_CS106B_set[0]
  
    # AND all previous individual constraints
    final_constraint_CS106B = solver.mkTerm(Kind.AND, constraint_CS106B, constraint_CS106B_set)

    solver.assertFormula(final_constraint_CS106B)

    # 2. ENGR40M or 76 An Intro to Making: What is EE? -OR- Information Science & Engineering:
    course_variable_ENGR40M = solver.mkConst(solver.getStringSort(), "ENGR40M")
    course_variable_76 = solver.mkConst(solver.getStringSort(), "76")
    course_variable_Info_Science = solver.mkConst(solver.getStringSort(), "Information Science & Engineering")
    
    # ENGR40M, 76, and Information Science & Engineering are \in transcript[*].Course_ID
    constraints_ENGR40M = [solver.mkTerm(Kind.EQUAL, course_variable_ENGR40M, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_76 = [solver.mkTerm(Kind.EQUAL, course_variable_76, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_Info_Science = [solver.mkTerm(Kind.EQUAL, course_variable_Info_Science, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
  
    if constraints_ENGR40M:
        constraint_ENGR40M = solver.mkTerm(Kind.OR, *constraints_ENGR40M) if len(constraints_ENGR40M) > 1 else constraints_ENGR40M[0]
    if constraints_76:
        constraint_76 = solver.mkTerm(Kind.OR, *constraints_76) if len(constraints_76) > 1 else constraints_76[0]
    if constraints_Info_Science:
        constraint_Info_Science = solver.mkTerm(Kind.OR, *constraints_Info_Science) if len(constraints_Info_Science) > 1 else constraints_Info_Science[0]
  
    # ENGR40M is in ENGR40M OR 76 is in 76 OR Information Science is in Info Science
    constraints_set_ENGR40M = [solver.mkTerm(Kind.EQUAL, course_variable_ENGR40M, solver.mkString("ENGR40M"))]
    constraints_set_76 = [solver.mkTerm(Kind.EQUAL, course_variable_76, solver.mkString("76"))]
    constraints_set_Info_Science = [solver.mkTerm(Kind.EQUAL, course_variable_Info_Science, solver.mkString("Information Science & Engineering"))]
  
    constraint_set_ENGR40M = constraints_set_ENGR40M[0]
    constraint_set_76 = constraints_set_76[0]
    constraint_set_Info_Science = constraints_set_Info_Science[0]
  
    # AND all previous individual constraints
    final_constraint_ENGR40M = solver.mkTerm(Kind.AND, constraint_ENGR40M, constraint_set_ENGR40M)
    final_constraint_76 = solver.mkTerm(Kind.AND, constraint_76, constraint_set_76)
    final_constraint_Info_Science = solver.mkTerm(Kind.AND, constraint_Info_Science, constraint_set_Info_Science)

    # Combine all constraints
    final_constraint_ENGR = solver.mkTerm(Kind.OR, final_constraint_ENGR40M, final_constraint_76, final_constraint_Info_Science)

    solver.assertFormula(final_constraint_ENGR)

    # Running the result checker with relevant variables
    variables = [course_variable_CS106B, course_variable_ENGR40M, course_variable_76, course_variable_Info_Science]
    result_checker(solver, variables)

# Test Case
transcript = {
    "Courses_Taken": [
        {"Course_ID": "CS106B"},
        {"Course_ID": "76"}
    ]
}

# Run the function with the test case
function(transcript)
