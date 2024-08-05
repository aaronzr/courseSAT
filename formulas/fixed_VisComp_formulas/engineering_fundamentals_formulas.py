
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

def math_requirement_formula(solver, transcript):
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Courses taken for Mathematics Requirement
    constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    math_constraints = [solver.mkTerm(Kind.OR, *constraints_set)]

    # Required course IDs for Mathematics
    math_required_courses = ['MATH19', 'MATH20', 'MATH21', 'CS103', 'CS109']

    # Course must be one of the required courses
    math_required_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course_id)) for course_id in math_required_courses]
    math_requirement = solver.mkTerm(Kind.OR, *math_required_constraints)

    # Combine constraints
    formula = solver.mkTerm(Kind.AND, *math_constraints, math_requirement)

    solver.assertFormula(formula)

def science_requirement_formula(solver, transcript):
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Courses taken for Science Requirement
    constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    science_constraints = [solver.mkTerm(Kind.OR, *constraints_set)]

    # Required Science courses
    science_required_courses = ['PHYS41', 'PHYS43']

    # Course must be one of the required Science courses
    science_required_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course_id)) for course_id in science_required_courses]
    science_requirement = solver.mkTerm(Kind.OR, *science_required_constraints)

    # Combine constraints
    formula = solver.mkTerm(Kind.AND, *science_constraints, science_requirement)

    solver.assertFormula(formula)

def tis_requirement_formula(solver, transcript):
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Courses taken for TiS Requirement
    constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    tis_constraints = [solver.mkTerm(Kind.OR, *constraints_set)]

    # Advisor approved TiS courses
    approved_tis_courses = ['Approved_TiS_Course_1', 'Approved_TiS_Course_2']

    # Course must be one of the approved TiS courses
    tis_approved_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course_id)) for course_id in approved_tis_courses]
    tis_requirement = solver.mkTerm(Kind.OR, *tis_approved_constraints)

    # Combine constraints
    formula = solver.mkTerm(Kind.AND, *tis_constraints, tis_requirement)

    solver.assertFormula(formula)

def eng_fundamentals_requirement_formula(solver, transcript):
    course_variable = solver.mkConst(solver.getStringSort(), "course")

    # Courses taken for Engineering Fundamentals Requirement
    constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    eng_fundamentals_constraints = [solver.mkTerm(Kind.OR, *constraints_set)]

    # Required Engineering Fundamentals courses
    eng_fundamentals_required_courses = ['CS106B', 'ENGR40', 'ENGR76']

    # Course must be one of the required Engineering Fundamentals courses
    eng_fundamentals_required_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course_id)) for course_id in eng_fundamentals_required_courses]
    eng_fundamentals_requirement = solver.mkTerm(Kind.OR, *eng_fundamentals_required_constraints)

    # Combine constraints
    formula = solver.mkTerm(Kind.AND, *eng_fundamentals_constraints, eng_fundamentals_requirement)

    solver.assertFormula(formula)

def function(transcript):
    solver = solver_init()

    # Apply the formulas to the solver for different requirements
    math_requirement_formula(solver, transcript)
    science_requirement_formula(solver, transcript)
    tis_requirement_formula(solver, transcript)
    eng_fundamentals_requirement_formula(solver, transcript)

    # Check the results
    result_checker(solver, [])

# Define a transcript schema for testing
transcript_schema = {
    "Courses_Taken": [
        {"Course_ID": "MATH19"},
        {"Course_ID": "MATH20"},
        {"Course_ID": "CS103"},
        {"Course_ID": "PHYS41"},
        {"Course_ID": "Approved_TiS_Course_1"},
        {"Course_ID": "ENGR40"}
    ]
}

# Run the function with the test transcript
function(transcript_schema)
