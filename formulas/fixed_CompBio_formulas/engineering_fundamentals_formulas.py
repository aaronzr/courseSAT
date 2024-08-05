
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

def create_and_formula(solver, constraints):
    if len(constraints) == 0:
        return solver.mkBoolean(True)  # No constraints, return TRUE
    elif len(constraints) == 1:
        return constraints[0]  # Single constraint, return it
    else:
        return solver.mkTerm(Kind.AND, *constraints)  # Multiple constraints, use AND

def create_or_formula(solver, constraints):
    if len(constraints) == 0:
        return solver.mkBoolean(False)  # No constraints, return FALSE
    elif len(constraints) == 1:
        return constraints[0]  # Single constraint, return it
    else:
        return solver.mkTerm(Kind.OR, *constraints)  # Multiple constraints, use OR

def function(transcript):
    solver = solver_init()

    # Define course variables
    course_vars = [solver.mkConst(solver.getStringSort(), f"course{i}") for i in range(1, 9)]
    course_vars.append(solver.mkConst(solver.getStringSort(), "course_tis"))
    course_vars.append(solver.mkConst(solver.getStringSort(), "course_elective"))

    # Mathematics Requirement
    constraints_sets = []
    for i in range(4):
        constraints_sets.append([
            solver.mkTerm(Kind.EQUAL, course_vars[i], solver.mkString(course.get("Course_ID")))
            for course in transcript.get("Courses_Taken", [])
        ])

    math_courses = ['MATH 19', 'MATH 20', 'MATH 21', 'CS103']
    math_constraints_set = [
        solver.mkTerm(Kind.EQUAL, course_vars[i], solver.mkString(course_unit))
        for i in range(4)
        for course_unit in math_courses
    ]

    formula_math = create_and_formula(solver, [
        create_or_formula(solver, cs) for cs in constraints_sets[:4]
    ] + [create_and_formula(solver, math_constraints_set)])
    solver.assertFormula(formula_math)

    # Science Requirement
    for i in range(4, 8):
        constraints_sets.append([
            solver.mkTerm(Kind.EQUAL, course_vars[i], solver.mkString(course.get("Course_ID")))
            for course in transcript.get("Courses_Taken", [])
        ])

    science_courses = ['BIO 82', 'BIO 83', 'BIO 85', 'BIO 86', 'HUMBIO 2A', 'HUMBIO 3A', 'HUMBIO 4A']
    science_constraints_set = [
        solver.mkTerm(Kind.EQUAL, course_vars[4], solver.mkString(course_unit))
        for course_unit in science_courses
    ]

    formula_science = create_and_formula(solver, [
        create_or_formula(solver, cs) for cs in constraints_sets[4:8]
    ] + [create_and_formula(solver, science_constraints_set)])
    solver.assertFormula(formula_science)

    # Technology in Society Requirement
    tis_constraints_set = [
        solver.mkTerm(Kind.EQUAL, course_vars[8], solver.mkString(course.get("Course_ID")))
        for course in transcript.get("Courses_Taken", [])
    ]
    tis_course = ['Technology in Society Course']
    tis_constraint_set = [
        solver.mkTerm(Kind.EQUAL, course_vars[8], solver.mkString(course_unit))
        for course_unit in tis_course
    ]

    formula_tis = create_and_formula(solver, [
        create_or_formula(solver, tis_constraints_set),
        create_and_formula(solver, tis_constraint_set)
    ])
    solver.assertFormula(formula_tis)

    # Engineering Fundamentals
    ef_constraints_set = [
        solver.mkTerm(Kind.EQUAL, course_vars[9], solver.mkString(course.get("Course_ID")))
        for course in transcript.get("Courses_Taken", [])
    ]
    ef_courses = ['CS106B', 'Elective']
    ef_constraint_set = [
        solver.mkTerm(Kind.EQUAL, course_vars[9], solver.mkString(course_unit))
        for course_unit in ef_courses
    ]

    formula_ef = create_and_formula(solver, [
        create_or_formula(solver, ef_constraints_set),
        create_and_formula(solver, ef_constraint_set)
    ])
    solver.assertFormula(formula_ef)

    # Check results
    result_checker(solver, course_vars)

# Sample transcript schema to test code correctness
transcript = {
    "Courses_Taken": [
        {"Course_ID": "MATH 19"},
        {"Course_ID": "MATH 20"},
        {"Course_ID": "MATH 21"},
        {"Course_ID": "CS103"},
        {"Course_ID": "BIO 82"},
        {"Course_ID": "BIO 83"},
        {"Course_ID": "HUMBIO 2A"},
        {"Course_ID": "HUMBIO 3A"},
        {"Course_ID": "Technology in Society Course"},
        {"Course_ID": "CS106B"},
        {"Course_ID": "Elective"}
    ]
}

function(transcript)
