
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
    
    # Choose 1 course from the TiS Approved list at ughb.stanford.edu the year taken
    course_variable = solver.mkConst(solver.getStringSort(), "selected_course")
    
    # selected_course is \in transcript[*].Courses_Taken.Course_ID
    course_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    if course_constraints:
        selected_course_constraint = solver.mkTerm(Kind.OR, *course_constraints)
    else:
        selected_course_constraint = solver.mkFalse()

    # selected_course is one of the TiS Approved list
    tis_approved_list = ['TiS Course 1', 'TiS Course 2', 'TiS Course 3']  # Add actual TiS approved courses
    tis_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course)) for course in tis_approved_list]
    if tis_constraints:
        tis_constraint = solver.mkTerm(Kind.OR, *tis_constraints)
    else:
        tis_constraint = solver.mkFalse()

    # All courses must be taken for a letter grade
    letter_grade_constraints = [solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString("Letter")) for course in transcript.get("Courses_Taken", [])]
    if len(letter_grade_constraints) > 1:
        grade_constraint = solver.mkTerm(Kind.AND, *letter_grade_constraints)
    elif letter_grade_constraints:
        grade_constraint = letter_grade_constraints[0]
    else:
        grade_constraint = solver.mkTrue()

    # Transfer and AP credits in Math, Science, Fundamentals, & TIS must be approved by the SoE Dean's Office
    transfer_approved_constraints = [solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Approval")), solver.mkString("Approved")) for course in transcript.get("Courses_Taken", []) if course.get("Type") in ["Transfer", "AP"]]
    if len(transfer_approved_constraints) > 1:
        transfer_approved_constraint = solver.mkTerm(Kind.AND, *transfer_approved_constraints)
    elif transfer_approved_constraints:
        transfer_approved_constraint = transfer_approved_constraints[0]
    else:
        transfer_approved_constraint = solver.mkTrue()

    # No course may be listed twice on the sheet
    unique_course_ids = {course.get("Course_ID") for course in transcript.get("Courses_Taken", [])}
    no_duplicates_constraint = solver.mkTerm(Kind.EQUAL, solver.mkInteger(len(unique_course_ids)), solver.mkInteger(len(transcript.get("Courses_Taken", []))))

    # Courses must be taken for the number of units on the Program Sheet
    specific_unit_constraints = []
    required_units = {
        'CS103': 5, 'CS106B': 5, 'CS107': 5, 
        'CS109': 5, 'CS111': 5, 'CS161': 5
    }
    for course in transcript.get("Courses_Taken", []):
        course_id = course.get("Course_ID")
        if course_id in required_units:
            specific_unit_constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkInteger(course.get("Units")), solver.mkInteger(required_units[course_id])))
    if len(specific_unit_constraints) > 1:
        specific_units_constraint = solver.mkTerm(Kind.AND, *specific_unit_constraints)
    elif specific_unit_constraints:
        specific_units_constraint = specific_unit_constraints[0]
    else:
        specific_units_constraint = solver.mkTrue()

    # Students without prior programming experience should first take CS106A
    prior_experience = transcript.get("Prior_Programming_Experience")
    if not prior_experience:
        prior_experience_courses = [solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), solver.mkString("CS106A")) for course in transcript.get("Courses_Taken", [])]
        if len(prior_experience_courses) > 1:
            prior_experience_constraint = solver.mkTerm(Kind.OR, *prior_experience_courses)
        elif prior_experience_courses:
            prior_experience_constraint = prior_experience_courses[0]
        else:
            prior_experience_constraint = solver.mkFalse()
    else:
        prior_experience_constraint = solver.mkTrue()

    # AND all constraints together
    final_constraints = [
        selected_course_constraint,
        tis_constraint,
        grade_constraint,
        transfer_approved_constraint,
        no_duplicates_constraint,
        specific_units_constraint,
        prior_experience_constraint
    ]

    final_constraint = solver.mkTerm(Kind.AND, *final_constraints)
    solver.assertFormula(final_constraint)

    variables = [course_variable]
    result_checker(solver, variables)

# Example transcript schema for testing
transcript_example = {
    "Courses_Taken": [
        {"Course_ID": "TiS Course 1", "Grade": "Letter", "Units": 5, "Type": "Regular"},
        {"Course_ID": "CS106A", "Grade": "Letter", "Units": 5, "Type": "Regular"},
        {"Course_ID": "CS107", "Grade": "Letter", "Units": 5, "Type": "Regular"}
    ],
    "Prior_Programming_Experience": False
}

# Run the function with the example transcript
function(transcript_example)
