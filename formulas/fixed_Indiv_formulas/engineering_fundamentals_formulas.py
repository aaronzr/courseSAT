
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

def sum_terms(solver, terms):
    if not terms:
        return solver.mkReal(0)
    sum_term = terms[0]
    for term in terms[1:]:
        sum_term = solver.mkTerm(Kind.ADD, sum_term, term)
    return sum_term

def function(transcript):
    solver = solver_init()

    ### Mathematics (26 units minimum)
    # Define variables for math courses
    math_course_variables = [solver.mkConst(solver.getStringSort(), f"math_course{i}") for i in range(1, 6)]

    # Constraints for each math course
    math_constraints = []
    for i, course in enumerate(["MATH19", "MATH20", "MATH21", "CS103", "CS109"]):
        math_constraints.append(solver.mkTerm(Kind.EQUAL, math_course_variables[i], solver.mkString(course)))

    # Additional constraints for total units
    total_math_units = solver.mkReal(26)
    math_units = [4, 4, 4, 5, 4]  # Units for each math course
    math_unit_terms = [solver.mkReal(math_units[i]) for i in range(5)]
    math_units_sum = sum_terms(solver, math_unit_terms)

    # Combine all constraints
    math_constraint_1 = solver.mkTerm(Kind.AND, *math_constraints)
    math_constraint_2 = solver.mkTerm(Kind.GEQ, math_units_sum, total_math_units)

    math_formula = solver.mkTerm(Kind.AND, math_constraint_1, math_constraint_2)
    solver.assertFormula(math_formula)

    ### Science (11 units minimum)
    # Define variables for science courses
    science_course_variables = [solver.mkConst(solver.getStringSort(), f"science_course{i}") for i in range(1, 4)]

    # Constraints for each science course
    science_constraints = []
    for i, course in enumerate(["PHYS41", "PHYS43", "Elective"]):
        science_constraints.append(solver.mkTerm(Kind.EQUAL, science_course_variables[i], solver.mkString(course)))

    # Additional constraints for total units
    total_science_units = solver.mkReal(11)
    science_units = [5, 5, 5]  # Units for each science course
    science_unit_terms = [solver.mkReal(science_units[i]) for i in range(3)]
    science_units_sum = sum_terms(solver, science_unit_terms)

    # Combine all constraints
    science_constraint_1 = solver.mkTerm(Kind.AND, *science_constraints)
    science_constraint_2 = solver.mkTerm(Kind.GEQ, science_units_sum, total_science_units)

    science_formula = solver.mkTerm(Kind.AND, science_constraint_1, science_constraint_2)
    solver.assertFormula(science_formula)

    ### Engineering Fundamentals (10 units minimum)
    # Define variables for engineering fundamentals courses
    eng_course_variables = [solver.mkConst(solver.getStringSort(), f"eng_course{i}") for i in range(1, 3)]

    # Constraints for each engineering course
    eng_constraints = []
    for i, course in enumerate(["CS106B", "ENGR40"]):
        eng_constraints.append(solver.mkTerm(Kind.EQUAL, eng_course_variables[i], solver.mkString(course)))

    # Additional constraints for total units
    total_eng_units = solver.mkReal(10)
    eng_units = [5, 5]  # Units for each engineering course
    eng_unit_terms = [solver.mkReal(eng_units[i]) for i in range(2)]
    eng_units_sum = sum_terms(solver, eng_unit_terms)

    # Combine all constraints
    eng_constraint_1 = solver.mkTerm(Kind.AND, *eng_constraints)
    eng_constraint_2 = solver.mkTerm(Kind.GEQ, eng_units_sum, total_eng_units)

    eng_formula = solver.mkTerm(Kind.AND, eng_constraint_1, eng_constraint_2)
    solver.assertFormula(eng_formula)

    # Collect all course variables to check
    all_course_variables = math_course_variables + science_course_variables + eng_course_variables

    # Check constraints
    result_checker(solver, all_course_variables)

# Example transcript data to pass into function
transcript = {
    "MATH19": 4,
    "MATH20": 4,
    "MATH21": 4,
    "CS103": 5,
    "CS109": 4,
    "PHYS41": 5,
    "PHYS43": 5,
    "Elective": 5,
    "CS106B": 5,
    "ENGR40": 5
}

# Run the function to verify correctness with example transcript
function(transcript)
