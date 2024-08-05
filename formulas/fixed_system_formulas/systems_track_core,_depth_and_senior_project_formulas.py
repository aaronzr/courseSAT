
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

def core_requirements(transcript):
    solver = solver_init()

    # Core Requirements
    course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
    course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")
    course_variable_3 = solver.mkConst(solver.getStringSort(), "course3")

    # CS107 or 107E: Computer Organization and Systems
    constraints_cs107 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("CS107")),
                         solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString("107E"))]

    # CS111: Operating Systems Principles
    constraints_cs111 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString("CS111"))]

    # CS161: Design and Analysis of Algorithms
    constraints_cs161 = [solver.mkTerm(Kind.EQUAL, course_variable_3, solver.mkString("CS161"))]

    constraint_cs107 = solver.mkTerm(Kind.OR, *constraints_cs107)  # Unpack list with *
    # Directly use cs111 constraint as there is only one
    constraint_cs111 = constraints_cs111[0]

    # If there is only one constraint, use it directly without Kind.OR
    if len(constraints_cs161) > 1:
        constraint_cs161 = solver.mkTerm(Kind.OR, *constraints_cs161)
    else:
        constraint_cs161 = constraints_cs161[0]

    # At least 15 units in Core Requirements
    course_units = [course.get("Earned_Units") for course in transcript.get("Courses_Taken", [])]
    total_units = sum(course_units)
    constraint_units = solver.mkTerm(Kind.GEQ, solver.mkInteger(total_units), solver.mkInteger(15))

    formula_core = solver.mkTerm(Kind.AND, constraint_cs107, constraint_cs111, constraint_cs161, constraint_units)
    solver.assertFormula(formula_core)

    return solver

def depth_requirements(transcript):
    solver = solver_init()

    track_requirement_a = solver.mkConst(solver.getStringSort(), "track_requirement_a")
    track_requirement_b = solver.mkConst(solver.getStringSort(), "track_requirement_b")

    # One of: CS 112 or 140E (Track Requirement A)
    constraints_track_requirement_a = [solver.mkTerm(Kind.EQUAL, track_requirement_a, solver.mkString("CS112")),
                                       solver.mkTerm(Kind.EQUAL, track_requirement_a, solver.mkString("140E"))]

    # One of: CS 143, EE 180 (Track Requirement B)
    constraints_track_requirement_b = [solver.mkTerm(Kind.EQUAL, track_requirement_b, solver.mkString("CS143")),
                                       solver.mkTerm(Kind.EQUAL, track_requirement_b, solver.mkString("EE180"))]

    constraint_track_requirement_a = solver.mkTerm(Kind.OR, *constraints_track_requirement_a)  # Unpack list with *
    constraint_track_requirement_b = solver.mkTerm(Kind.OR, *constraints_track_requirement_b)

    # At least 25 units in Depth Requirements
    course_units = [course.get("Earned_Units") for course in transcript.get("Courses_Taken", [])]
    total_units = sum(course_units)
    constraint_units = solver.mkTerm(Kind.GEQ, solver.mkInteger(total_units), solver.mkInteger(25))

    formula_depth = solver.mkTerm(Kind.AND, constraint_track_requirement_a, constraint_track_requirement_b, constraint_units)
    solver.assertFormula(formula_depth)

    return solver

def senior_project_requirement(transcript):
    solver = solver_init()

    senior_project_units = solver.mkConst(solver.getIntegerSort(), "senior_project_units")
    senior_project_courses = ["CS191", "CS191W", "CS194", "CS194H", "CS194W", "CS210B", "CS294"]

    # At least 3 units of Senior Project Course
    constraints_senior_project = [
        course.get("Earned_Units")
        for course in transcript.get("Courses_Taken", [])
        if course.get("Course_ID") in senior_project_courses
    ]

    total_senior_project_units = sum(constraints_senior_project)
    formula_senior_project = solver.mkTerm(Kind.GEQ, solver.mkInteger(total_senior_project_units), solver.mkInteger(3))
    solver.assertFormula(formula_senior_project)

    return solver

# Test Scripts (Sample JSON transcript):

sample_transcript_core = {
    "Courses_Taken": [
        {"Course_ID": "CS107", "Earned_Units": 5},
        {"Course_ID": "CS111", "Earned_Units": 5},
        {"Course_ID": "CS161", "Earned_Units": 5}
    ]
}

sample_transcript_depth = {
    "Courses_Taken": [
        {"Course_ID": "CS112", "Earned_Units": 10},
        {"Course_ID": "CS143", "Earned_Units": 15}
    ]
}

sample_transcript_senior = {
    "Courses_Taken": [
        {"Course_ID": "CS191", "Earned_Units": 3}
    ]
}

# Running and checking results
core_solver = core_requirements(sample_transcript_core)
result_checker(core_solver, [])

depth_solver = depth_requirements(sample_transcript_depth)
result_checker(depth_solver, [])

senior_solver = senior_project_requirement(sample_transcript_senior)
result_checker(senior_solver, [])
