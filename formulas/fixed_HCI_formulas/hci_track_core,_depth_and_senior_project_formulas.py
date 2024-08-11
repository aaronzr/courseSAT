
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

def generate_constraint_course_taken(solver, course_id, courses_taken):
    course_variable = solver.mkConst(solver.getStringSort(), course_id)
    constraints_set = [
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) 
        for course in courses_taken
    ]
    return solver.mkTerm(Kind.OR, *constraints_set)

def generate_core_constraints(solver, transcript):
    courses_taken = transcript.get("Courses_Taken", [])
    
    # CS107 or 107E
    constraint_cs107 = generate_constraint_course_taken(solver, "cs107", courses_taken)
    constraint_cs107e = generate_constraint_course_taken(solver, "cs107e", courses_taken)
    solver.assertFormula(solver.mkTerm(Kind.OR, constraint_cs107, constraint_cs107e))
    
    # CS111
    constraint_cs111 = generate_constraint_course_taken(solver, "cs111", courses_taken)
    solver.assertFormula(constraint_cs111)
    
    # CS161
    constraint_cs161 = generate_constraint_course_taken(solver, "cs161", courses_taken)
    solver.assertFormula(constraint_cs161)
    
    # Advisor approval
    advisor_approval = transcript.get("Approval", [])
    if advisor_approval:
        for approval in advisor_approval:
            approval_variable = solver.mkBoolean(approval.get("Approved"))
            solver.assertFormula(approval_variable)
    
    # Deviations
    deviations = transcript.get("Deviations", [])
    if deviations:
        for deviation in deviations:
            deviation_variable = solver.mkBoolean(deviation.get("Approved"))
            solver.assertFormula(deviation_variable)

def function(transcript):
    solver = solver_init()
    generate_core_constraints(solver, transcript)
    return result_checker(solver, [])

# Example transcript schema for testing
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "HCI",
        "StudentID": 12345,
        "Coterm": False
    },
    "Courses_Taken": [
        {"Course_ID": "cs107", "Title": "Computer Organization and Systems", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": "cs111", "Title": "Operating Systems Principles", "Earned_Units": 5, "Grade": "B"},
        {"Course_ID": "cs161", "Title": "Design and Analysis of Algorithms", "Earned_Units": 5, "Grade": "A"}
    ],
    "Approval": [
        {"Approved": True, "Approved_By": "Advisor Name", "Approved_Course_ID": "cs161"}
    ],
    "Deviations": [
        {"Deviated_Course_ID": "cs111", "Approved": True, "Approved_By": "Advisor Name"}
    ]
}

# Check HCI Track Core requirements with the provided transcript schema
function(transcript)
