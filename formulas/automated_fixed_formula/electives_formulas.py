
import os
import sys
import json
import cvc5
from cvc5 import Kind

# Initialize the solver with relevant options
def solver_init():
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver

# Function to check result of the solver and print model or unsatisfiable core
def result_checker(solver, variables=None):
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

# Function to add constraints to solver
def function(transcript):
    solver = solver_init()
    
    # Define constraints within this function using the provided transcript schema
    def add_constraints(solver, transcript):
        # Constraint: All courses submitted for the MSCS degree must be numbered 100 or greater.
        constraints_set1 = [solver.mkTerm(
            Kind.GEQ, 
            solver.mkReal(course["Course_ID"]),
            solver.mkReal(100)
        ) for course in transcript["Courses_Taken"]]
        constraint_1 = solver.mkTerm(Kind.AND, *constraints_set1)
        solver.assertFormula(constraint_1)
        
        # Constraint: At most 10 units of Foundations requirement courses may be counted toward 45 units.
        max_foundation_units = 10
        foundation_courses = []  # Assume foundation courses are identified, add logic if necessary
        foundation_units_sum = sum([course["Earned_Units"] for course in foundation_courses])
        foundation_constraint = solver.mkTerm(
            Kind.LEQ,
            solver.mkReal(foundation_units_sum),
            solver.mkReal(max_foundation_units)
        )
        solver.assertFormula(foundation_constraint)
        
        # Constraint: At most 3 units of 1-2 unit seminars may be counted toward 45 units.
        seminar_courses = [course for course in transcript["Courses_Taken"] if 1 <= course["Earned_Units"] <= 2]
        seminar_units_sum = sum([course["Earned_Units"] for course in seminar_courses])
        seminar_constraint = solver.mkTerm(
            Kind.LEQ,
            solver.mkReal(seminar_units_sum),
            solver.mkReal(3)
        )
        solver.assertFormula(seminar_constraint)

        # Constraint: At least 36 units must be taken for a letter grade (or CR or S in specified terms)
        letter_grade_units_min = 36
        letter_grades = ['A', 'B', 'C', 'D', 'F']  # Add 'CR' and 'S' for specific terms (Spring 19-20 and Fall-Summer 20-21)
        letter_grade_courses = [course for course in transcript["Courses_Taken"] if course["Grade"] in letter_grades]
        letter_grade_units_sum = sum([course["Earned_Units"] for course in letter_grade_courses])
        letter_grade_constraint = solver.mkTerm(
            Kind.GEQ,
            solver.mkReal(letter_grade_units_sum),
            solver.mkReal(letter_grade_units_min)
        )
        solver.assertFormula(letter_grade_constraint)

        # Constraint: Average grade must be at least B (3.0 in Stanford’s GPA scale)
        total_units = sum([course["Earned_Units"] for course in transcript["Courses_Taken"]])
        earned_grade_points = {
            'A': 4.0, 'B': 3.0, 'C': 2.0, 'D': 1.0, 'F': 0.0,
            'CR': 3.0, 'S': 3.0  # Assuming specific CR/S terms as 3.0 for computational convenience
        }
        grade_points_sum = sum([earned_grade_points[course["Grade"]] * course["Earned_Units"] for course in transcript["Courses_Taken"] if course["Grade"] in earned_grade_points])
        average_grade = grade_points_sum / total_units
        grade_constraint = solver.mkTerm(
            Kind.GEQ,
            solver.mkReal(average_grade),
            solver.mkReal(3.0)
        )
        solver.assertFormula(grade_constraint)

        # Constraint: Units previously applied toward BS requirements may not also be counted toward the MSCS.
        bs_units = 0  # To be dynamically checked or estimated in a real scenario.
        ms_units_constraint = solver.mkTerm(
            Kind.EQUAL,
            solver.mkReal(bs_units),
            solver.mkReal(0)
        )
        solver.assertFormula(ms_units_constraint)

        # Constraint: At least 45 graduate units at Stanford are required for the MSCS degree
        grad_units_min = 45
        total_units_earned = sum([course["Earned_Units"] for course in transcript["Courses_Taken"]])
        grad_units_constraint = solver.mkTerm(
            Kind.GEQ,
            solver.mkReal(total_units_earned),
            solver.mkReal(grad_units_min)
        )
        solver.assertFormula(grad_units_constraint)

        # Constraints for electives and advisor approval
        cs_courses = ["CS196", "CS198", "CS390A", "CS390B", "CS390C"]
        advisor_approval = transcript["Approval"]
        deviations = transcript["Deviations"]
        for course in transcript["Courses_Taken"]:
            advisor_constraints = []
            if course["Course_ID"] in cs_courses:
                advisor_constraints.append(any(a["Approved"] for a in advisor_approval if a["Approved_Course_ID"] == course["Course_ID"]))
            for dev in deviations:
                if dev["Deviated_Course_ID"] == course["Course_ID"] and dev["Approved"]:
                    advisor_constraints.append(True)
            advisor_constraint = solver.mkTerm(Kind.AND, *advisor_constraints) if advisor_constraints else solver.mkBoolean(True)
            solver.assertFormula(advisor_constraint)

    # Add constraints to the solver based on the transcript
    add_constraints(solver, transcript)
    
    # Check the satisfiability and print the result
    result_checker(solver)
    
    
# Sample transcript schema for testing
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "MSCS",
        "StudentID": 123456,
        "Coterm": False
    },
    "AP_Credits": [
        {"Advanced_Placement": "Math", "Earned_Units": 8}
    ],
    "Courses_Taken": [
        {"Course_ID": 113, "Title": "Intro to AI", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": 210, "Title": "Advanced Algorithms", "Earned_Units": 3, "Grade": "B"},
        {"Course_ID": 299, "Title": "Special Seminar", "Earned_Units": 2, "Grade": "S"},
        {"Course_ID": 101, "Title": "Data Structures", "Earned_Units": 4, "Grade": "A"},
        {"Course_ID": 102, "Title": "Operating Systems", "Earned_Units": 4, "Grade": "B"},
        {"Course_ID": 105, "Title": "Web Development", "Earned_Units": 3, "Grade": "C"},
        {"Course_ID": 107, "Title": "Mobile App Development", "Earned_Units": 3, "Grade": "A"}
    ],
    "Deviations": [
        {"Deviated_Course_ID": "None", "Approved": False, "Approved_By": "None"},
        {"Deviated_Course_ID": "CS 250", "Approved": True, "Approved_By": "Advisor_Name"},
    ],
    "Approval": [
        {"Approved": True, "Approved_By": "Advisor_Name", "Approved_Course_ID": "CS 250"}
    ],
    "Cumulative_GPA": {
        "Undergrad": 3.5,
        "Graduate": 3.2,
    }
}

# Run the function with the sample transcript to test
function(transcript)
