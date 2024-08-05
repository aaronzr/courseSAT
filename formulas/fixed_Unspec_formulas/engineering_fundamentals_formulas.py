
import os
import sys
import cvc5
import json
from cvc5 import Kind

# Function to initialize the solver
def solver_init(): 
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver 

# Function to check the result from the solver
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
    
    # Constraint for CS106B Programming Abstractions
    course_variable_CS106B = solver.mkConst(solver.getStringSort(), "CS106B")
    # CS106B is \in transcript[*].course
    constraints_set_CS106B = [solver.mkTerm(Kind.EQUAL, course_variable_CS106B, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_CS106B = solver.mkTerm(Kind.OR, *constraints_set_CS106B) if constraints_set_CS106B else solver.mkFalse()
    # CS106B must be taken
    constraint_CS106B_units = solver.mkTerm(Kind.EQUAL, course_variable_CS106B, solver.mkString("CS106B"))

    # Formulate the final formula for CS106B requirement
    formula_CS106B = solver.mkTerm(Kind.AND, constraint_CS106B, constraint_CS106B_units)
    solver.assertFormula(formula_CS106B)

    # Constraint for ENGR40M or 76
    course_variable_ENGR40M = solver.mkConst(solver.getStringSort(), "ENGR40M")
    course_variable_ENGR76 = solver.mkConst(solver.getStringSort(), "ENGR76")
    # ENGR40M is \in transcript[*].course
    # ENGR76 is \in transcript[*].course
    constraints_set_ENGR40M = [solver.mkTerm(Kind.EQUAL, course_variable_ENGR40M, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set_ENGR76 = [solver.mkTerm(Kind.EQUAL, course_variable_ENGR76, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_ENGR40M = solver.mkTerm(Kind.OR, *constraints_set_ENGR40M) if constraints_set_ENGR40M else solver.mkFalse()
    constraint_ENGR76 = solver.mkTerm(Kind.OR, *constraints_set_ENGR76) if constraints_set_ENGR76 else solver.mkFalse()
    # ENGR40M or ENGR76 must be taken
    constraint_ENGR_units = solver.mkTerm(Kind.OR, solver.mkTerm(Kind.EQUAL, course_variable_ENGR40M, solver.mkString("ENGR40M")), solver.mkTerm(Kind.EQUAL, course_variable_ENGR76, solver.mkString("ENGR76")))

    # Formulate the final formula for ENGR40M or 76 requirement
    formula_ENGR = solver.mkTerm(Kind.AND, solver.mkTerm(Kind.OR, constraint_ENGR40M, constraint_ENGR76), constraint_ENGR_units)
    solver.assertFormula(formula_ENGR)

    # Check and print result
    result_checker(solver, [course_variable_CS106B, course_variable_ENGR40M, course_variable_ENGR76])


# Test case to verify the correctness
if __name__ == '__main__':
    # Sample transcript data structure
    sample_transcript = {
        "Courses_Taken": [
            {"Course_ID": "CS106B"},
            {"Course_ID": "ENGR40M"},
            # Add more courses as needed
        ]
    }
    
    function(sample_transcript)
