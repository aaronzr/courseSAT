
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

def generate_solver_formulas(transcript):
    solver = solver_init()
    
    # Course variables for CS107, CS111, CS161
    cs107_variable = solver.mkConst(solver.getStringSort(), "cs107_course")
    cs111_variable = solver.mkConst(solver.getStringSort(), "cs111_course")
    cs161_variable = solver.mkConst(solver.getStringSort(), "cs161_course")
    
    # Constraints for CS107, CS111, CS161 courses
    constraints_set_cs107 = [solver.mkTerm(Kind.EQUAL, cs107_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set_cs111 = [solver.mkTerm(Kind.EQUAL, cs111_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set_cs161 = [solver.mkTerm(Kind.EQUAL, cs161_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    
    constraint_cs107 = solver.mkTerm(Kind.OR, *constraints_set_cs107)
    constraint_cs111 = solver.mkTerm(Kind.OR, *constraints_set_cs111)
    constraint_cs161 = solver.mkTerm(Kind.OR, *constraints_set_cs161)
    
    # Constraints for CS107 or 107E, CS111, CS161
    cs107_constraint = solver.mkTerm(Kind.OR, solver.mkTerm(Kind.EQUAL, cs107_variable, solver.mkString("CS107")), solver.mkTerm(Kind.EQUAL, cs107_variable, solver.mkString("CS107E")))
    
    cs107_cs111_cs161_formula = solver.mkTerm(Kind.AND, cs107_constraint, constraint_cs107, constraint_cs111, constraint_cs161)
    
    # Assert the formula
    solver.assertFormula(cs107_cs111_cs161_formula)
    
    # Add more constraints for other requirements here
    
    return solver

# Example usage
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "Computer Science",
        "StudentID": 12345,
        "Coterm": False
    },
    "Courses_Taken": [
        {"Course_ID": "CS107", "Title": "Computer Organization and Systems", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": "CS111", "Title": "Operating Systems Principles", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": "CS161", "Title": "Design and Analysis of Algorithms", "Earned_Units": 5, "Grade": "A"}
    ]
}

solver = generate_solver_formulas(transcript)

# Check satisfiability
sat = solver.checkSat()
if sat.isSat():
    print("Transcript satisfies the Theory Track Core requirements.")
else:
    print("Transcript does not satisfy the Theory Track Core requirements.")
