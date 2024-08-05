
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
        print("Unsat requirement core is:", core)
    return result

def function(transcript):
    solver = solver_init()

    # Define course variables
    course_variable_CS106B = solver.mkConst(solver.getStringSort(), "course_CS106B")
    course_variable_ENGR40M = solver.mkConst(solver.getStringSort(), "course_ENGR40M")
    course_variable_InformationScience = solver.mkConst(solver.getStringSort(), "course_InformationScience")
    
    # Define units variables
    units_variable_CS106B = solver.mkConst(solver.getIntegerSort(), "units_CS106B")
    units_variable_ENGR40M = solver.mkConst(solver.getIntegerSort(), "units_ENGR40M")
    units_variable_InformationScience = solver.mkConst(solver.getIntegerSort(), "units_InformationScience")
    total_units = solver.mkConst(solver.getIntegerSort(), "total_units")

    # Constraints for CS106B
    constraint_CS106B = solver.mkTerm(Kind.EQUAL, course_variable_CS106B, solver.mkString("CS 106B"))
    constraint_units_CS106B = solver.mkTerm(Kind.EQUAL, units_variable_CS106B, solver.mkInteger(5))

    # Constraints for ENGR40M or ENGR76 or Information Science+
    constraint_ENGR40M = solver.mkTerm(Kind.EQUAL, course_variable_ENGR40M, solver.mkString("ENGR40M"))
    constraint_ENGR76 = solver.mkTerm(Kind.EQUAL, course_variable_ENGR40M, solver.mkString("ENGR76"))
    constraint_InfoScience = solver.mkTerm(Kind.EQUAL, course_variable_InformationScience, solver.mkString("Information Science+"))
    constraint_units_ENGR40M = solver.mkTerm(Kind.EQUAL, units_variable_ENGR40M, solver.mkInteger(5))
    constraint_units_InfoScience = solver.mkTerm(Kind.EQUAL, units_variable_InformationScience, solver.mkInteger(5))

    # Constraint for total units minimum requirement
    constraint_total_units = solver.mkTerm(Kind.GEQ, total_units, solver.mkInteger(10))

    # Minimum GPA constraint (assuming it's a constant value)
    constraint_min_GPA = solver.mkTerm(Kind.GEQ, solver.mkReal("2.0"), solver.mkReal("2.0"))

    # Combine all constraints
    constraints = [constraint_CS106B, constraint_units_CS106B, 
                   solver.mkTerm(Kind.OR, constraint_ENGR40M, constraint_ENGR76, constraint_InfoScience),
                   constraint_units_ENGR40M, constraint_units_InfoScience, constraint_total_units, constraint_min_GPA]

    # Assert all constraints
    for constraint in constraints:
        solver.assertFormula(constraint)

    # Check satisfiability
    result = result_checker(solver, [course_variable_CS106B, course_variable_ENGR40M, course_variable_InformationScience, units_variable_CS106B, units_variable_ENGR40M, units_variable_InformationScience, total_units])
    if result.isSat():
        print("Transcript schema satisfies the Engineering Fundamentals requirements.")
    else:
        print("Transcript schema does not satisfy the Engineering Fundamentals requirements.")

# Example transcript schema to test code correctness
transcript = {
    "courses": ["CS 106B", "ENGR40M"],
    "units": {
        "CS 106B": 5,
        "ENGR40M": 5
    },
    "total_units": 10,
    "gpa": 3.0
}

function(transcript)
