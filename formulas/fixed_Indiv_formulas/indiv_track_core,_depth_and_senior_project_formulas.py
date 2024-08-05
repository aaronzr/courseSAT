
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
    
    # Generate core constraint
    course_variable = solver.mkConst(solver.getStringSort(), "course")
    # Constraint for CS107, CS107E, CS111, CS161
    core_constraints = [
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString("CS107")),
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString("CS107E")),
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString("CS111")),
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString("CS161"))
    ]
    core_constraint = solver.mkTerm(Kind.OR, *core_constraints)
    solver.assertFormula(core_constraint)
    
    # Placeholder for Depth constraint
    # Add formula for Depth constraint here if needed in the future

    # Generate senior project constraint
    senior_project_courses = ["CS191", "CS191W", "CS194", "CS194H", "CS194W", "CS210B", "CS294"]
    senior_project_constraints = [
        solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course))
        for course in senior_project_courses
    ]
    senior_project_constraint = solver.mkTerm(Kind.OR, *senior_project_constraints)
    solver.assertFormula(senior_project_constraint)
    
    # Check results
    result_checker(solver, [course_variable])

# Sample transcript schema to test the formulas
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "Computer Science",
        "StudentID": 12345,
        "Coterm": False
    },
    "AP_Credits": [],
    "Courses_Taken": [
        {"Course_ID": "CS107", "Title": "Computer Organization and Systems", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": "CS111", "Title": "Operating Systems Principles", "Earned_Units": 4, "Grade": "B"},
        # Add more courses taken if needed
    ],
    "Deviations": [
        {
            "Deviated_Course_ID": "CS101",
            "Approved": True,
            "Approved_By": "Advisor"
        }
    ],
    "Approval": [
        {
            "Approved": True,
            "Approved_By": "Advisor",
            "Approved_Course_ID": "CS107"
        }
    ],
    "Cumulative_GPA": {
        "Undergrad": 3.7,
        "Graduate": 0
    }
}

function(transcript)
