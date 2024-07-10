
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

    # Helper Function to Assert Course Constraints
    def course_constraint(course_title, valid_titles):
        course_var = solver.mkConst(solver.getStringSort(), course_title)
        constraints = [solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(course["Title"])) for course in transcript.get("Courses_Taken", [])]
        if len(constraints) == 0:
            return solver.mkFalse(), course_var
        elif len(constraints) == 1:
            return constraints[0], course_var
        else:
            return solver.mkTerm(Kind.OR, *constraints), course_var

    # List the required courses and their equivalent titles
    required_courses = {
        "Logic, Automata & Complexity": ["CS103"],
        "Probability": ["CS109", "Stat116", "CME106", "MS&E220", "EE178"],
        "Algorithmic Analysis": ["CS161"],
        "Computer Organ & Sys": ["CS107", "CS107E"],
        "Principles of Computer Systems": ["CS110", "CS111"],
    }

    course_vars = {}
    course_constraints = []
    for course_title, valid_titles in required_courses.items():
        constraint, course_var = course_constraint(course_title, valid_titles)
        course_constraints.append(constraint)
        course_vars[course_title] = course_var

    # Combine all course constraints
    if len(course_constraints) == 1:
        all_course_constraints = course_constraints[0]
    else:
        all_course_constraints = solver.mkTerm(Kind.AND, *course_constraints)

    # Constraint to check that total units do not exceed 10 units
    total_units_var = solver.mkConst(solver.getRealSort(), "total_units")
    all_units = [solver.mkReal(course["Earned_Units"]) for course in transcript.get("Courses_Taken", [])]

    # Sum of units calculation
    if len(all_units) > 1:
        overall_units_sum = solver.mkTerm(Kind.ADD, *all_units)
    elif len(all_units) == 1:
        overall_units_sum = all_units[0]
    else:
        overall_units_sum = solver.mkReal(0)

    # Sum of units constraint
    sum_units_constraint = solver.mkTerm(Kind.LEQ, overall_units_sum, solver.mkReal(10))

    # Combine all constraints
    overall_constraint = solver.mkTerm(Kind.AND, all_course_constraints, sum_units_constraint)

    # Check for advisor approval on deviations
    def advisor_approval_constraint():
        approval_constraints = []
        for approval in transcript.get("Approval", []):
            is_approved = solver.mkBoolean(approval["Approved"])
            if is_approved:
                approved_course_id = solver.mkString(approval["Approved_Course_ID"])
                approval_constraints.append(solver.mkTerm(Kind.EQUAL, approved_course_id, solver.mkString("CS103")))  # Example
        if len(approval_constraints) > 1:
            return solver.mkTerm(Kind.AND, *approval_constraints)
        elif len(approval_constraints) == 1:
            return approval_constraints[0]
        return solver.mkTrue()

    # Get the final approval constraint
    final_approval_constraint = advisor_approval_constraint()

    # Add approval constraints to the overall constraint
    final_constraint = solver.mkTerm(Kind.AND, overall_constraint, final_approval_constraint)

    # Assert the final constraint to the solver
    solver.assertFormula(final_constraint)

    # Check satisfiability and return the result
    return result_checker(solver, list(course_vars.values()))

# Test case to validate correctness
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "CS Masters",
        "StudentID": 123456,
        "Coterm": False
    },
    "AP_Credits": [
        {"Advanced_Placement": "CS", "Earned_Units": 5}
    ],
    "Courses_Taken": [
        {"Course_ID": 103, "Title": "CS103", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": 109, "Title": "CS109", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": 161, "Title": "CS161", "Earned_Units": 3, "Grade": "A"}
        # Add more courses as needed
    ],
    "Deviations": [
        {"Deviated_Course_ID": "None", "Approved": False, "Approved_By": "None"},
    ],
    "Approval": [
        {"Approved": True, "Approved_By": "Advisor", "Approved_Course_ID": "CS103"}
    ],
    "Cumulative_GPA": {
        "Undergrad": 3.5,
        "Graduate": 4.0,
    },
}

# Execute the function to check satisfiability for the sample transcript
function(transcript)
