
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
    print("Satisfiability: ", result)
    if result.isSat():
        print("SAT")
        if variables:
            for variable in variables:
                model = solver.getValue(variable)
                print(f"Model for {variable}: {model}")
    else:
        core = solver.getUnsatCore()
        print("Unsat requirement core is: ", core)

    return result

def ensure_or_constraints(solver, constraints):
    # Ensure that constraints list conforms to OR term requirement
    if len(constraints) == 0:
        # Add a false dummy term to handle cases where there are no constraints
        constraints.append(solver.mkBoolean(False))
    elif len(constraints) == 1:
        # Add a true dummy term to handle cases where there is exactly one constraint
        constraints.append(solver.mkBoolean(True))
    return constraints

def function(transcript):
    solver = solver_init()
    
    # Core (15 units minimum):
    core_course_variable = solver.mkConst(solver.getStringSort(), "core_course")
    core_constraints_set = [solver.mkTerm(Kind.EQUAL, core_course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    core_constraints_set = ensure_or_constraints(solver, core_constraints_set)
    core_constraint = solver.mkTerm(Kind.OR, *core_constraints_set)
    
    core_constraints_list = [solver.mkString("CS107"), solver.mkString("107E"), solver.mkString("CS111"), solver.mkString("CS161")]
    core_constraint_course_list = [solver.mkTerm(Kind.EQUAL, core_course_variable, course) for course in core_constraints_list]
    core_constraint_course_list = ensure_or_constraints(solver, core_constraint_course_list)

    core_constraint_core = solver.mkTerm(Kind.OR, *core_constraint_course_list)
    core_final_constraint = solver.mkTerm(
        Kind.AND,
        core_constraint,
        core_constraint_core
    )
    solver.assertFormula(core_final_constraint)

    # Depth; Track and Electives (25 units and seven courses minimum):
    # Track Requirement A: CS154 Intro Automata and Complexity Theory
    track_a_course_variable = solver.mkConst(solver.getStringSort(), "track_a_course")
    track_a_constraints_set = [solver.mkTerm(Kind.EQUAL, track_a_course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    track_a_constraints_set = ensure_or_constraints(solver, track_a_constraints_set)
    track_a_constraint = solver.mkTerm(Kind.OR, *track_a_constraints_set)
    
    track_a_constraints_list = [solver.mkString("CS154")]
    track_a_constraint_course_list = [solver.mkTerm(Kind.EQUAL, track_a_course_variable, course) for course in track_a_constraints_list]
    track_a_constraint_course_list = ensure_or_constraints(solver, track_a_constraint_course_list)
    
    track_a_constraint_core = solver.mkTerm(Kind.OR, *track_a_constraint_course_list)
    track_a_final_constraint = solver.mkTerm(
        Kind.AND,
        track_a_constraint,
        track_a_constraint_core
    )
    solver.assertFormula(track_a_final_constraint)

    # Track Requirement B: One of CS 112, 140E, or 143
    track_b_course_variable = solver.mkConst(solver.getStringSort(), "track_b_course")
    track_b_constraints_set = [solver.mkTerm(Kind.EQUAL, track_b_course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    track_b_constraints_set = ensure_or_constraints(solver, track_b_constraints_set)
    track_b_constraint = solver.mkTerm(Kind.OR, *track_b_constraints_set)
    
    track_b_constraints_list = [solver.mkString("CS112"), solver.mkString("CS140E"), solver.mkString("CS143")]
    track_b_constraint_course_list = [solver.mkTerm(Kind.EQUAL, track_b_course_variable, course) for course in track_b_constraints_list]
    track_b_constraint_course_list = ensure_or_constraints(solver, track_b_constraint_course_list)
    
    track_b_constraint_core = solver.mkTerm(Kind.OR, *track_b_constraint_course_list)
    track_b_final_constraint = solver.mkTerm(
        Kind.AND,
        track_b_constraint,
        track_b_constraint_core
    )
    solver.assertFormula(track_b_final_constraint)

    # Add other track and elective constraints similarly
    # ...

    # Senior Project (1 course required):
    senior_project_variable = solver.mkConst(solver.getStringSort(), "senior_project_course")
    senior_project_constraints_set = [solver.mkTerm(Kind.EQUAL, senior_project_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    senior_project_constraints_set = ensure_or_constraints(solver, senior_project_constraints_set)
    senior_project_constraint = solver.mkTerm(Kind.OR, *senior_project_constraints_set)
    
    senior_project_constraints_list = [solver.mkString("191"), solver.mkString("191W"), solver.mkString("194"), solver.mkString("194H"), solver.mkString("194W"), solver.mkString("210B"), solver.mkString("294")]
    senior_project_constraint_course_list = [solver.mkTerm(Kind.EQUAL, senior_project_variable, course) for course in senior_project_constraints_list]
    senior_project_constraint_course_list = ensure_or_constraints(solver, senior_project_constraint_course_list)

    senior_project_constraint_course = solver.mkTerm(Kind.OR, *senior_project_constraint_course_list)
    senior_project_final_constraint = solver.mkTerm(
        Kind.AND,
        senior_project_constraint,
        senior_project_constraint_course
    )
    solver.assertFormula(senior_project_final_constraint)

    # Check results
    result_checker(solver, [core_course_variable, track_a_course_variable, track_b_course_variable, senior_project_variable])

# Sample transcript to test
transcript = {
    "Courses_Taken": [
        {"Course_ID": "CS107"},
        {"Course_ID": "CS154"},
        {"Course_ID": "CS112"},
        {"Course_ID": "191"}
    ]
}

# Run function with sample transcript
function(transcript)
