
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

def check_requirements(transcript):
    solver = solver_init()

    # Define course IDs, names, units, and grades based on transcript
    course_ids = [solver.mkConst(solver.getStringSort(), f"course_{i}_id") for i in range(len(transcript['Courses_Taken']))]
    course_names = [solver.mkConst(solver.getStringSort(), f"course_{i}_name") for i in range(len(transcript['Courses_Taken']))]
    course_units = [solver.mkConst(solver.getStringSort(), f"course_{i}_units") for i in range(len(transcript['Courses_Taken']))]
    course_grades = [solver.mkConst(solver.getStringSort(), f"course_{i}_grade") for i in range(len(transcript['Courses_Taken']))]

    # Assert the constraints for each course taken
    for i, course in enumerate(transcript['Courses_Taken']):
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, course_ids[i], solver.mkString(course['Course_ID'])))
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, course_names[i], solver.mkString(course['Title'])))
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, course_units[i], solver.mkString(course['Earned_Units'])))
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, course_grades[i], solver.mkString(course['Grade'])))

    ### Foundations Requirement ###
    foundations_courses = [
        'CS103', 'CS109', 'Stat116', 'CME106',
        'MS&E220', 'EE178', 'CS161',
        'CS107', 'CS107E', 'CS110', 'CS111'
    ]
    total_foundations_units = solver.mkConst(solver.getIntegerSort(), "total_foundations_units")
    foundations_course_conditions = [solver.mkTerm(Kind.EQUAL, course_ids[i], solver.mkString(course)) for i in range(len(course_ids)) for course in foundations_courses]
    total_foundation_units_condition = solver.mkTerm(Kind.LEQ, total_foundations_units, solver.mkInteger(10))
    
    solver.assertFormula(solver.mkTerm(Kind.OR, *foundations_course_conditions))
    solver.assertFormula(total_foundation_units_condition)

    ### Significant Implementation Requirement ###
    significant_impl_courses = [
        'CS140', 'CS140E', 'CS143', 'CS144', 'CS145',
        'CS148', 'CS151', 'CS190', 'CS210B', 'CS212',
        'CS221', 'CS227B', 'CS231N', 'CS243', 'CS248',
        'CS248A', 'CS341'
    ]
    significant_impl_conditions = [solver.mkTerm(Kind.EQUAL, course_ids[i], solver.mkString(course)) for i in range(len(course_ids)) for course in significant_impl_courses]
    sig_impl_unit_condition = [solver.mkTerm(Kind.GT, course_grades[i], solver.mkString('B')) for i in range(len(course_grades))]

    solver.assertFormula(solver.mkTerm(Kind.OR, *significant_impl_conditions))
    solver.assertFormula(solver.mkTerm(Kind.AND, *sig_impl_unit_condition))

    ### Breadth Requirement ###
    breadth_areas = {
        'A': ['CS154', 'CS157', 'CS168'],
        'B': ['CS140', 'CS140E', 'CS143'],
        'C': ['CS145', 'CS147', 'CS148'],
        'D': ['CS152', 'CS181', 'CS182']
    }
    breadth_conditions = []
    for area_key, courses in breadth_areas.items():
        area_conditions = [solver.mkTerm(Kind.EQUAL, course_ids[i], solver.mkString(course)) for i in range(len(course_ids)) for course in courses]
        unit_conditions = [solver.mkTerm(Kind.GE, course_units[i], solver.mkInteger(3)) for i in range(len(course_units))]
        breadth_conditions.append(solver.mkTerm(Kind.AND, solver.mkTerm(Kind.OR, *area_conditions), solver.mkTerm(Kind.AND, *unit_conditions)))

    solver.assertFormula(solver.mkTerm(Kind.AND, *breadth_conditions))

    ### Artificial Intelligence Depth Requirement ###
    ai_depth_courses = [
        'CS221', 'CS223A', 'CS224N', 'CS224S', 'CS224U', 'CS224V',
        'CS224W', 'CS228', 'CS229', 'CS231A', 'CS231N', 'CS234',
        'CS237A', 'CS237B', 'CS238'
    ]
    total_ai_depth_units = solver.mkConst(solver.getIntegerSort(), "total_ai_depth_units")
    ai_depth_course_conditions = [solver.mkTerm(Kind.EQUAL, course_ids[i], solver.mkString(course)) for i in range(len(course_ids)) for course in ai_depth_courses]
    
    total_ai_depth_units_condition = solver.mkTerm(Kind.GE, total_ai_depth_units, solver.mkInteger(21))

    solver.assertFormula(solver.mkTerm(Kind.OR, *ai_depth_course_conditions))
    solver.assertFormula(total_ai_depth_units_condition)

    ### Elective Requirement ###
    elective_courses_conditions = [solver.mkTerm(Kind.GT, course_ids[i], solver.mkInteger(111)) for i in range(len(course_ids))]
    elective_courses_exclusion = [
        'CS196', 'CS198', 'CS390A', 'CS390B', 'CS390C'
    ]
    elective_courses_exclusion_conditions = [solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_ids[i], solver.mkString(course))) for i in range(len(course_ids)) for course in elective_courses_exclusion]

    solver.assertFormula(solver.mkTerm(Kind.OR, *elective_courses_conditions))
    solver.assertFormula(solver.mkTerm(Kind.AND, *elective_courses_exclusion_conditions))

    ### Additional Requirements ###
    total_units = solver.mkConst(solver.getIntegerSort(), "total_units")
    grad_gpa = solver.mkConst(solver.getRealSort(), "grad_gpa")
    total_letter_units = solver.mkConst(solver.getIntegerSort(), "total_letter_units")

    condition_min_total_units = solver.mkTerm(Kind.GE, total_units, solver.mkInteger(45))
    condition_min_letter_grade_units = solver.mkTerm(Kind.GE, total_letter_units, solver.mkInteger(36))
    condition_min_gpa = solver.mkTerm(Kind.GE, grad_gpa, solver.mkReal(3.0))

    solver.assertFormula(condition_min_total_units)
    solver.assertFormula(condition_min_letter_grade_units)
    solver.assertFormula(condition_min_gpa)

    ### Deviations ###
    for deviation in transcript['Deviations']:
        if deviation['Approved']:
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, deviate_course, solver.mkString(deviation['Deviated_Course_ID'])))
        else:
            solver.assertFormula(solver.mkFalse())

    result = result_checker(solver, course_ids + course_names + course_units + course_grades)
    
    return result

# Define a sample transcript to test the function
transcript = {
    "Student": {
        "Name": "John Doe",
        "Program": "Artificial Intelligence",
        "StudentID": 123456,
        "Coterm": False
    },
    "AP_Credits": [],
    "Courses_Taken": [
        {"Course_ID": "CS103", "Title": "Logic", "Earned_Units": 4, "Grade": "A"},
        {"Course_ID": "CS109", "Title": "Probability", "Earned_Units": 5, "Grade": "B"},
        {"Course_ID": "CS161", "Title": "Algorithmic Analysis", "Earned_Units": 3, "Grade": "A"},
        # Add more courses here
    ],
    "Deviations": [],
    "Approval": [],
    "Cumulative_GPA": {
        "Undergrad": 3.5,
        "Graduate": 3.5,
    },
}

# Run the function with the sample transcript
result = check_requirements(transcript)
print(f"Satisfiability: {result}")
