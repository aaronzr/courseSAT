
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

    ### Mathematics (26 units minimum) ###

    # MATH19 Calculus
    math19_variable = solver.mkConst(solver.getStringSort(), "MATH19")
    constraints_set_math19 = [solver.mkTerm(Kind.EQUAL, math19_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math19 = solver.mkTerm(Kind.OR, *constraints_set_math19)
    solver.assertFormula(constraint_math19)

    # MATH20
    math20_variable = solver.mkConst(solver.getStringSort(), "MATH20")
    constraints_set_math20 = [solver.mkTerm(Kind.EQUAL, math20_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math20 = solver.mkTerm(Kind.OR, *constraints_set_math20)
    solver.assertFormula(constraint_math20)

    # MATH21
    math21_variable = solver.mkConst(solver.getStringSort(), "MATH21")
    constraints_set_math21 = [solver.mkTerm(Kind.EQUAL, math21_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math21 = solver.mkTerm(Kind.OR, *constraints_set_math21)
    solver.assertFormula(constraint_math21)

    # CS103 Mathematical Foundations of Computing
    cs103_variable = solver.mkConst(solver.getStringSort(), "CS103")
    constraints_set_cs103 = [solver.mkTerm(Kind.EQUAL, cs103_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs103 = solver.mkTerm(Kind.OR, *constraints_set_cs103)
    solver.assertFormula(constraint_cs103)

    # CS109 Introduction to Probability for Computer Scientists
    cs109_variable = solver.mkConst(solver.getStringSort(), "CS109")
    constraints_set_cs109 = [solver.mkTerm(Kind.EQUAL, cs109_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs109 = solver.mkTerm(Kind.OR, *constraints_set_cs109)
    solver.assertFormula(constraint_cs109)

    # Mathematics Elective 1
    math_elective_1_variable = solver.mkConst(solver.getStringSort(), "Math_Elective_1")
    constraints_set_math_elective_1 = [solver.mkTerm(Kind.EQUAL, math_elective_1_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math_elective_1 = solver.mkTerm(Kind.OR, *constraints_set_math_elective_1)
    solver.assertFormula(constraint_math_elective_1)

    # Mathematics Elective 2
    math_elective_2_variable = solver.mkConst(solver.getStringSort(), "Math_Elective_2")
    constraints_set_math_elective_2 = [solver.mkTerm(Kind.EQUAL, math_elective_2_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math_elective_2 = solver.mkTerm(Kind.OR, *constraints_set_math_elective_2)
    solver.assertFormula(constraint_math_elective_2)

    ### Science (11 units minimum) ###

    # PHYS41 Mechanics
    phys41_variable = solver.mkConst(solver.getStringSort(), "PHYS41")
    constraints_set_phys41 = [solver.mkTerm(Kind.EQUAL, phys41_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_phys41 = solver.mkTerm(Kind.OR, *constraints_set_phys41)
    solver.assertFormula(constraint_phys41)

    # PHYS43 Electricity and Magnetism
    phys43_variable = solver.mkConst(solver.getStringSort(), "PHYS43")
    constraints_set_phys43 = [solver.mkTerm(Kind.EQUAL, phys43_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_phys43 = solver.mkTerm(Kind.OR, *constraints_set_phys43)
    solver.assertFormula(constraint_phys43)

    # Science Elective
    science_elective_variable = solver.mkConst(solver.getStringSort(), "Science_Elective")
    constraints_set_science_elective = [solver.mkTerm(Kind.EQUAL, science_elective_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_science_elective = solver.mkTerm(Kind.OR, *constraints_set_science_elective)
    solver.assertFormula(constraint_science_elective)

    ### Technology in Society Requirement ###

    # TiS Course
    tis_course_variable = solver.mkConst(solver.getStringSort(), "TiS_Course")
    constraints_set_tis_course = [solver.mkTerm(Kind.EQUAL, tis_course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_tis_course = solver.mkTerm(Kind.OR, *constraints_set_tis_course)
    solver.assertFormula(constraint_tis_course)

    ### Engineering Fundamentals (10 units minimum) ###

    # CS106B Programming Abstractions
    cs106b_variable = solver.mkConst(solver.getStringSort(), "CS106B")
    constraints_set_cs106b = [solver.mkTerm(Kind.EQUAL, cs106b_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs106b = solver.mkTerm(Kind.OR, *constraints_set_cs106b)
    solver.assertFormula(constraint_cs106b)

    # ENGR40M or 76 An Intro to Making or Information Science & Engr
    engr_fund_variable = solver.mkConst(solver.getStringSort(), "ENGR_Fundamental")
    constraints_set_engr_fund = [solver.mkTerm(Kind.EQUAL, engr_fund_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraint_engr_fund = solver.mkTerm(Kind.OR, *constraints_set_engr_fund)
    solver.assertFormula(constraint_engr_fund)

    variables = [
        math19_variable, math20_variable, math21_variable, cs103_variable,
        cs109_variable, math_elective_1_variable, math_elective_2_variable,
        phys41_variable, phys43_variable, science_elective_variable, tis_course_variable,
        cs106b_variable, engr_fund_variable
    ]

    return result_checker(solver, variables)

# Test case
if __name__ == "__main__":
    test_transcript = {
        "Courses_Taken": [
            {"Course_ID": "MATH19"},
            {"Course_ID": "MATH20"},
            {"Course_ID": "MATH21"},
            {"Course_ID": "CS103"},
            {"Course_ID": "CS109"},
            {"Course_ID": "MATH_ELECTIVE_1"},
            {"Course_ID": "MATH_ELECTIVE_2"},
            {"Course_ID": "PHYS41"},
            {"Course_ID": "PHYS43"},
            {"Course_ID": "SCIENCE_ELECTIVE"},
            {"Course_ID": "TIS_COURSE"},
            {"Course_ID": "CS106B"},
            {"Course_ID": "ENGR_Fundamental"}
        ]
    }
    function(test_transcript)
