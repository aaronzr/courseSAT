
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
    
    # Constraint for MATH19 Calculus
    math19_variable = solver.mkConst(solver.getStringSort(), "MATH19")
    constraints_math19 = [solver.mkTerm(Kind.EQUAL, math19_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math19 = solver.mkTerm(Kind.OR, *constraints_math19)
    
    # Constraint for MATH20
    math20_variable = solver.mkConst(solver.getStringSort(), "MATH20")
    constraints_math20 = [solver.mkTerm(Kind.EQUAL, math20_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math20 = solver.mkTerm(Kind.OR, *constraints_math20)
    
    # Constraint for MATH21
    math21_variable = solver.mkConst(solver.getStringSort(), "MATH21")
    constraints_math21 = [solver.mkTerm(Kind.EQUAL, math21_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math21 = solver.mkTerm(Kind.OR, *constraints_math21)
    
    # Constraint for CS103 Mathematical Foundations of Computing
    cs103_variable = solver.mkConst(solver.getStringSort(), "CS103")
    constraints_cs103 = [solver.mkTerm(Kind.EQUAL, cs103_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs103 = solver.mkTerm(Kind.OR, *constraints_cs103)
    
    # Constraint for CS109 Introduction to Probability for Computer Scientists
    cs109_variable = solver.mkConst(solver.getStringSort(), "CS109")
    constraints_cs109 = [solver.mkTerm(Kind.EQUAL, cs109_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs109 = solver.mkTerm(Kind.OR, *constraints_cs109)
    
    # Constraint for Plus two electives from Math 51, 52, 53, 104, 107, 108, 109, 110, 113; CS 157, 205L; PHIL 151; CME 100, 102, 104; ENGR 108
    electives_count = 0
    electives_variables = []
    elective_constraints = []
    for elective_course in ['Math 51', 'Math 52', 'Math 53', 'Math 104', 'Math 107', 'Math 108', 'Math 109', 'Math 110', 'Math 113', 'CS 157', 'CS 205L', 'PHIL 151', 'CME 100', 'CME 102', 'CME 104', 'ENGR 108']:
        elective_variable = solver.mkConst(solver.getStringSort(), elective_course)
        electives_variables.append(elective_variable)
        constraints_elective = [solver.mkTerm(Kind.EQUAL, elective_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
        constraint_elective = solver.mkTerm(Kind.OR, *constraints_elective)
        elective_constraints.append(constraint_elective)
    
    constraint_electives = solver.mkTerm(Kind.GEQ, solver.mkInteger(electives_count), solver.mkInteger(2))

    # Advisor approval constraint
    math_advisor_approval = solver.mkConst(solver.getBooleanSort(), "Math_Advisor_Approval")
    advisor_approval_formula_math = solver.mkTerm(Kind.EQUAL, math_advisor_approval, solver.mkBoolean(transcript["Advisor_Approval"]["Mathematics"]))
    
    # Deviation constraint
    math_deviated_course = solver.mkConst(solver.getStringSort(), "Math_Deviated_Course")
    math_deviated_approval = solver.mkConst(solver.getBooleanSort(), "Math_Deviated_Approval")
    deviation_formula_math = solver.mkTerm(Kind.ITE, math_deviated_approval, solver.mkTerm(Kind.EQUAL, math_deviated_course, solver.mkString(transcript["Deviations"][0]["Deviated_Course_ID"])), solver.mkTrue())
    
    # All constraints for Mathematics
    all_math_constraints = [constraint_math19, constraint_math20, constraint_math21, constraint_cs103, constraint_cs109, constraint_electives, advisor_approval_formula_math, deviation_formula_math]
    
    # Constraint for PHYS41 Mechanics (or PHYS 21 or PHYS 61)
    physics_mechanics_variable = solver.mkConst(solver.getStringSort(), "PHYS41")
    constraints_physics_mechanics = [solver.mkTerm(Kind.EQUAL, physics_mechanics_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_mechanics = solver.mkTerm(Kind.OR, *constraints_physics_mechanics)
    
    physics_21_variable = solver.mkConst(solver.getStringSort(), "PHYS21")
    constraints_physics_21 = [solver.mkTerm(Kind.EQUAL, physics_21_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_21 = solver.mkTerm(Kind.OR, *constraints_physics_21)
    
    physics_61_variable = solver.mkConst(solver.getStringSort(), "PHYS61")
    constraints_physics_61 = [solver.mkTerm(Kind.EQUAL, physics_61_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_61 = solver.mkTerm(Kind.OR, *constraints_physics_61)
    
    # Constraint for PHYS43 Electricity and Magnetism (or PHYS 23 or PHYS 81/63)
    physics_electromagnetism_variable = solver.mkConst(solver.getStringSort(), "PHYS43")
    constraints_physics_electromagnetism = [solver.mkTerm(Kind.EQUAL, physics_electromagnetism_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_electromagnetism = solver.mkTerm(Kind.OR, *constraints_physics_electromagnetism)
    
    physics_23_variable = solver.mkConst(solver.getStringSort(), "PHYS23")
    constraints_physics_23 = [solver.mkTerm(Kind.EQUAL, physics_23_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_23 = solver.mkTerm(Kind.OR, *constraints_physics_23)
    
    physics_81_63_variable = solver.mkConst(solver.getStringSort(), "PHYS8163")
    constraints_physics_81_63 = [solver.mkTerm(Kind.EQUAL, physics_81_63_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_81_63 = solver.mkTerm(Kind.OR, *constraints_physics_81_63)
    
    # Constraint for One elective from the SoE Science List, PSYCH 30, or AP Chemistry
    science_electives_count = 0
    science_electives_variables = []
    for science_elective_course in ['SoE Science List', 'PSYCH 30', 'AP Chemistry']:
        science_elective_variable = solver.mkConst(solver.getStringSort(), science_elective_course)
        science_electives_variables.append(science_elective_variable)
        constraints_science_elective = [solver.mkTerm(Kind.EQUAL, science_elective_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
        constraint_science_elective = solver.mkTerm(Kind.OR, *constraints_science_elective)
        if any(constraints_science_elective):  # Corrected this line to check if any constraint is true
            science_electives_count += 1
    
    # Ensure at least one science elective is taken
    constraint_science_electives = solver.mkTerm(Kind.GEQ, solver.mkInteger(science_electives_count), solver.mkInteger(1))
    
    # Advisor approval constraint
    science_advisor_approval = solver.mkConst(solver.getBooleanSort(), "Science_Advisor_Approval")
    advisor_approval_formula_science = solver.mkTerm(Kind.EQUAL, science_advisor_approval, solver.mkBoolean(transcript["Advisor_Approval"]["Science"]))
    
    # Deviation constraint
    science_deviated_course = solver.mkConst(solver.getStringSort(), "Science_Deviated_Course")
    science_deviated_approval = solver.mkConst(solver.getBooleanSort(), "Science_Deviated_Approval")
    deviation_formula_science = solver.mkTerm(Kind.ITE, science_deviated_approval, solver.mkTerm(Kind.EQUAL, science_deviated_course, solver.mkString(transcript["Deviations"][0]["Deviated_Course_ID"])), solver.mkTrue())
    
    # All constraints for Science
    all_science_constraints = [constraint_physics_mechanics, constraint_physics_21, constraint_physics_61, constraint_physics_electromagnetism, constraint_physics_23, constraint_physics_81_63, constraint_science_electives, advisor_approval_formula_science, deviation_formula_science]
    
    # Combine all constraints
    all_constraints = all_math_constraints + all_science_constraints
    
    # Add all constraints to the solver
    for constraint in all_constraints:
        solver.assertFormula(constraint)
    
    # Check satisfiability of all constraints
    result_checker(solver, None)


# Test transcript schema for correctness
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "Engineering",
        "StudentID": 123456,
        "Coterm": False
    },
    "AP_Credits": [
        {"Advanced_Placement": "AP Calculus", "Earned_Units": 5}
    ],
    "Courses_Taken": [
        {"Course_ID": "MATH19", "Title": "CS 101", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": "MATH20", "Title": "MATH 101", "Earned_Units": 5, "Grade": "B"},
        {"Course_ID": "MATH21", "Title": "MATH 102", "Earned_Units": 5, "Grade": "C"},
        {"Course_ID": "CS103", "Title": "CS 103", "Earned_Units": 5, "Grade": "Z"},
        {"Course_ID": "CS109", "Title": "CS 109", "Earned_Units": 5, "Grade": "A"},
        {"Course_ID": "Math 52", "Title": "Math 52", "Earned_Units": 5, "Grade": "B"},
        {"Course_ID": "PHYS41", "Title": "Physics 41", "Earned_Units": 5, "Grade": "A"}
    ],
    "Deviations": [
        {"Deviated_Course_ID": "PHYS 101", "Approved": False, "Approved_By": "Advisor A"}
    ],
    "Advisor_Approval": {
        "Mathematics": True,
        "Science": False
    },
    "Cumulative_GPA": {
        "Undergrad": 3.5,
        "Graduate": 0.0
    }
}

function(transcript)
