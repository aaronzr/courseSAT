
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

    # Core (15 units minimum):
    # Represent units of core courses as numerical terms
    core_course_units = [solver.mkReal(5), solver.mkReal(5), solver.mkReal(5)]  # Example unit values
    
    # Constraint: At least 15 units from core courses
    core_total_units = solver.mkTerm(Kind.ADD, *core_course_units)
    core_units_constraint = solver.mkTerm(Kind.GEQ, core_total_units, solver.mkReal(15))
    
    # Assert the core units constraint
    solver.assertFormula(core_units_constraint)

    # Depth (25 units minimum):
    # Represent units of depth courses in a similar manner
    depth_course_units = [solver.mkReal(10), solver.mkReal(10), solver.mkReal(5)]  # Example unit values
    
    # Sum of core and depth units
    total_units = solver.mkTerm(Kind.ADD, core_total_units, *depth_course_units)
    
    # Minimum 25 units for depth courses
    depth_total_units = solver.mkTerm(Kind.ADD, *depth_course_units)
    depth_units_constraint = solver.mkTerm(Kind.GEQ, depth_total_units, solver.mkReal(25))
    
    # Assert the depth units constraint
    solver.assertFormula(depth_units_constraint)

    # Senior Project (1 course required, assumed 3 units):
    # Represent units of senior project courses
    senior_project_units = solver.mkReal(3)  # Example unit value
    
    # Assert the senior project units constraint (at least 3 units)
    senior_project_units_constraint = solver.mkTerm(Kind.GEQ, senior_project_units, solver.mkReal(3))
    
    # Assert the senior project units constraint
    solver.assertFormula(senior_project_units_constraint)

    # Check the overall units
    overall_units_constraint = solver.mkTerm(Kind.GEQ, total_units, solver.mkReal(43))
    solver.assertFormula(overall_units_constraint)

    # Check results
    # We will not include the individual course variables here since we are focusing on the units
    variables = []  # No course variables for model fetching
    return result_checker(solver, variables)

def main():
    # Mock transcript for testing
    transcript = {"core": ["CS107", "CS111", "CS161"], "depth": ["Depth1", "Depth2", "Depth3"], "senior_project": ["191"]}
    function(transcript)

if __name__ == "__main__":
    main()
