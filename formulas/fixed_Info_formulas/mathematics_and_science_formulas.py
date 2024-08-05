
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
    variables = []

    # Mathematics Requirement:
    ## MATH19: Calculus
    calculus_course_variable = solver.mkConst(solver.getStringSort(), "Calculus")
    variables.append(calculus_course_variable)
    constraints_set_calculus = [solver.mkTerm(Kind.EQUAL, calculus_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_calculus = solver.mkTerm(Kind.OR, *constraints_set_calculus)
    solver.assertFormula(constraint_calculus)

    ## MATH20
    math20_course_variable = solver.mkConst(solver.getStringSort(), "Math20")
    variables.append(math20_course_variable)
    constraints_set_math20 = [solver.mkTerm(Kind.EQUAL, math20_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math20 = solver.mkTerm(Kind.OR, *constraints_set_math20)
    solver.assertFormula(constraint_math20)

    ## MATH21
    math21_course_variable = solver.mkConst(solver.getStringSort(), "Math21")
    variables.append(math21_course_variable)
    constraints_set_math21 = [solver.mkTerm(Kind.EQUAL, math21_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math21 = solver.mkTerm(Kind.OR, *constraints_set_math21)
    solver.assertFormula(constraint_math21)

    ## CS103 Mathematical Foundations of Computing
    cs103_course_variable = solver.mkConst(solver.getStringSort(), "CS103")
    variables.append(cs103_course_variable)
    constraints_set_cs103 = [solver.mkTerm(Kind.EQUAL, cs103_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs103 = solver.mkTerm(Kind.OR, *constraints_set_cs103)
    solver.assertFormula(constraint_cs103)

    ## CS109 Introduction to Probability for Computer Scientists
    cs109_course_variable = solver.mkConst(solver.getStringSort(), "CS109")
    variables.append(cs109_course_variable)
    constraints_set_cs109 = [solver.mkTerm(Kind.EQUAL, cs109_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs109 = solver.mkTerm(Kind.OR, *constraints_set_cs109)
    solver.assertFormula(constraint_cs109)

    ## Plus two electives
    elective1_variable = solver.mkConst(solver.getStringSort(), "Elective1")
    elective2_variable = solver.mkConst(solver.getStringSort(), "Elective2")
    variables.append(elective1_variable)
    variables.append(elective2_variable)
    # Course is \in transcript[*].course
    constraints_set_elective1 = [solver.mkTerm(Kind.EQUAL, elective1_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set_elective2 = [solver.mkTerm(Kind.EQUAL, elective2_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_elective1 = solver.mkTerm(Kind.OR, *constraints_set_elective1)
    constraint_elective2 = solver.mkTerm(Kind.OR, *constraints_set_elective2)
    # Course 1 != Course 2
    constraint_diff_electives = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, elective1_variable, elective2_variable))
    solver.assertFormula(constraint_diff_electives)
    solver.assertFormula(constraint_elective1)
    solver.assertFormula(constraint_elective2)

    # Science Requirement:
    ## PHYS41 Mechanics
    mechanics_course_variable = solver.mkConst(solver.getStringSort(), "Mechanics")
    variables.append(mechanics_course_variable)
    constraints_set_mechanics = [solver.mkTerm(Kind.EQUAL, mechanics_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_mechanics = solver.mkTerm(Kind.OR, *constraints_set_mechanics)
    solver.assertFormula(constraint_mechanics)

    ## PHYS43 Electricity and Magnetism
    electricity_course_variable = solver.mkConst(solver.getStringSort(), "Electricity")
    variables.append(electricity_course_variable)
    constraints_set_electricity = [solver.mkTerm(Kind.EQUAL, electricity_course_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_electricity = solver.mkTerm(Kind.OR, *constraints_set_electricity)
    solver.assertFormula(constraint_electricity)

    ## Elective
    science_elective_variable = solver.mkConst(solver.getStringSort(), "ScienceElective")
    variables.append(science_elective_variable)
    constraints_set_science_elective = [solver.mkTerm(Kind.EQUAL, science_elective_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_science_elective = solver.mkTerm(Kind.OR, *constraints_set_science_elective)
    solver.assertFormula(constraint_science_elective)

    # Advisor Approval and Deviation Constraints:
    ## Advisor Approval
    advisor_approval_constraint = solver.mkConst(solver.getBooleanSort(), "AdvisorApproval")
    solver.assertFormula(advisor_approval_constraint)

    ## Deviation Constraints
    for deviation in transcript.get("Deviations", []):
        if deviation.get("Approved", False) == False:
            dev_course_variable = solver.mkConst(solver.getStringSort(), f"DevCourse_{deviation.get('Deviated_Course_ID')}")
            constraints_set_dev = [solver.mkTerm(Kind.EQUAL, dev_course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
            constraint_dev = solver.mkTerm(Kind.OR, *constraints_set_dev)
            solver.assertFormula(constraint_dev)

    result_checker(solver, variables)


# Test case to verify correctness
transcript_example = {
    "Courses_Taken": [
        {"Title": "Calculus"},
        {"Title": "Math20"},
        {"Title": "Math21"},
        {"Title": "CS103"},
        {"Title": "CS109"},
        {"Title": "Elective1_Title"},
        {"Title": "Elective2_Title"},
        {"Title": "Mechanics"},
        {"Title": "Electricity"},
        {"Title": "ScienceElective_Title"}
    ],
    "Deviations": [
        {"Deviated_Course_ID": "1", "Course_ID": "SomeDevCourse", "Approved": True}
    ]
}

function(transcript_example)
