
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
    
    # ------ Mathematics Requirement ------
    # Extract courses taken from the transcript
    courses_taken = [(course.get("Course_ID"), course.get("Units")) for course in transcript.get("Courses_Taken", [])]

    # Define the list of required math courses
    math_courses = {
        'MATH19': 5,
        'MATH20': 5,
        'MATH21': 5,
        'CS103': 5,
        'CS109': 6
    }
    math_units_required = 26

    # Declare variables for math elective courses
    math_elective_1 = solver.mkConst(solver.getStringSort(), "math_elective_1")
    math_elective_2 = solver.mkConst(solver.getStringSort(), "math_elective_2")

    # Constraints for required math courses
    math_course_constraints = [solver.mkTerm(Kind.EQUAL, solver.mkString(course), solver.mkString(course)) for course, units in courses_taken if course in math_courses]
    
    # Create terms for unit values and sum them
    math_units_sum = solver.mkTerm(Kind.ADD, *[solver.mkInteger(units) for course, units in courses_taken if course in math_courses])
    math_units_constraint = solver.mkTerm(Kind.GEQ, math_units_sum, solver.mkInteger(math_units_required))

    # Define the list of possible math elective courses (example list)
    math_elective_courses = {
        'MATH104': 5,
        'MATH105': 5,
        'MATH106': 6
    }

    # Constraints for math electives
    math_elective_constraints = [solver.mkTerm(Kind.EQUAL, math_elective_1, solver.mkString(course_id)) for course_id in math_elective_courses]
    math_elective_constraints += [solver.mkTerm(Kind.EQUAL, math_elective_2, solver.mkString(course_id)) for course_id in math_elective_courses]
    math_elective_distinct = solver.mkTerm(Kind.DISTINCT, math_elective_1, math_elective_2)
    
    # Combine all constraints
    math_formula = solver.mkTerm(Kind.AND, *math_course_constraints, math_units_constraint, *math_elective_constraints, math_elective_distinct)

    # Assert the formula
    solver.assertFormula(math_formula)

    # ------ Science Requirement ------
    # Define the required science courses
    science_courses = {
        'PHYS41': 6,
        'PHYS43': 5
    }
    science_units_required = 11

    # Declare a variable for the science elective course
    science_elective = solver.mkConst(solver.getStringSort(), "science_elective")

    # Constraints for required science courses
    science_course_constraints = [solver.mkTerm(Kind.EQUAL, solver.mkString(course), solver.mkString(course)) for course, units in courses_taken if course in science_courses]
    
    # Create terms for unit values and sum them
    science_units_sum = solver.mkTerm(Kind.ADD, *[solver.mkInteger(units) for course, units in courses_taken if course in science_courses])
    science_units_constraint = solver.mkTerm(Kind.GEQ, science_units_sum, solver.mkInteger(science_units_required))

    # Define the list of possible science elective courses (example list)
    science_elective_courses = {
        'BIO101': 5,
        'CHEM101': 6,
        'PHYS102': 6
    }

    # Constraints for the science elective
    science_elective_constraints = [solver.mkTerm(Kind.EQUAL, science_elective, solver.mkString(course_id)) for course_id in science_elective_courses]

    # Combine all constraints
    science_formula = solver.mkTerm(Kind.AND, *science_course_constraints, science_units_constraint, *science_elective_constraints)

    # Assert the formula
    solver.assertFormula(science_formula)

    # ------ Technology in Society Requirement ------
    # Define the list of approved TiS courses (example list)
    approved_tis_courses = ['STS101', 'PHIL102']

    # Declare a variable for the TiS course
    tis_course = solver.mkConst(solver.getStringSort(), "tis_course")

    # Constraints for the TiS course
    tis_course_constraints = [solver.mkTerm(Kind.EQUAL, tis_course, solver.mkString(course_id)) for course_id in approved_tis_courses]

    # Combine all constraints
    tis_formula = solver.mkTerm(Kind.OR, *tis_course_constraints)

    # Assert the formula
    solver.assertFormula(tis_formula)

    # ------ Engineering Fundamentals Requirement ------
    # Define the list of required engineering courses
    eng_fund_courses = {
        'CS106B': 5,
        'ENGR40': 5,
        'ENGR76': 5
    }
    eng_units_required = 10

    # Declare variables for engineering electives (example list)
    intro_making_course = solver.mkConst(solver.getStringSort(), "intro_making_course")
    info_science_course = solver.mkConst(solver.getStringSort(), "info_science_course")

    # Constraints for required engineering courses
    eng_course_constraints = [solver.mkTerm(Kind.EQUAL, solver.mkString(course), solver.mkString(course)) for course, units in courses_taken if course in eng_fund_courses]
    
    # Create terms for unit values and sum them
    eng_units_sum = solver.mkTerm(Kind.ADD, *[solver.mkInteger(units) for course, units in courses_taken if course in eng_fund_courses])
    eng_units_constraint = solver.mkTerm(Kind.GEQ, eng_units_sum, solver.mkInteger(eng_units_required))

    # Define the list of possible engineering elective courses (example list)
    eng_elective_courses = {
        'ENGR110': 5,
        'ENGR111': 5
    }

    # Constraints for engineering electives
    eng_elective_constraints = [solver.mkTerm(Kind.EQUAL, intro_making_course, solver.mkString(course_id)) for course_id in eng_elective_courses]
    eng_elective_constraints += [solver.mkTerm(Kind.EQUAL, info_science_course, solver.mkString(course_id)) for course_id in eng_elective_courses]
    eng_elective_distinct = solver.mkTerm(Kind.DISTINCT, intro_making_course, info_science_course)
    
    # Combine all constraints
    eng_formula = solver.mkTerm(Kind.AND, *eng_course_constraints, eng_units_constraint, *eng_elective_constraints, eng_elective_distinct)

    # Assert the formula
    solver.assertFormula(eng_formula)

    return result_checker(solver, [math_elective_1, math_elective_2, science_elective, tis_course, intro_making_course, info_science_course])

# Test case: Create a sample transcript
sample_transcript = {
    "Courses_Taken": [
        {"Course_ID": "MATH19", "Units": 5},
        {"Course_ID": "MATH20", "Units": 5},
        {"Course_ID": "MATH21", "Units": 5},
        {"Course_ID": "CS103", "Units": 5},
        {"Course_ID": "CS109", "Units": 6},
        {"Course_ID": "MATH104", "Units": 5},
        {"Course_ID": "PHYS41", "Units": 6},
        {"Course_ID": "PHYS43", "Units": 5},
        {"Course_ID": "BIO101", "Units": 5},
        {"Course_ID": "CS106B", "Units": 5},
        {"Course_ID": "ENGR40", "Units": 5},
        {"Course_ID": "STS101", "Units": 5},
        {"Course_ID": "ENGR110", "Units": 5}
    ]
}

# Run the function with the sample transcript
result = function(sample_transcript)
print("Final Result:", result)
