
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
    
    # Required Course CS 221 or approved equivalent.
    req_course_221 = solver.mkConst(solver.getStringSort(), "req_course_221")
    cs_221_in_transcript = [solver.mkTerm(Kind.EQUAL, req_course_221, solver.mkString(course.get("Course_ID")))for course in transcript.get("Courses_Taken", [])]
    cs_221_approved = solver.mkTerm(Kind.OR, 
        solver.mkTerm(Kind.AND, 
            solver.mkTerm(Kind.EQUAL, solver.mkString("CS 221"), req_course_221), 
            solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, req_course_221, solver.mkString("None")))
        ), 
        solver.mkTerm(Kind.AND, 
            solver.mkTerm(Kind.EQUAL, solver.mkString("None"), req_course_221), 
            solver.mkTerm(Kind.OR, *[solver.mkTerm(Kind.AND, 
                solver.mkTerm(Kind.EQUAL, 
                    solver.mkString(deviation.get("Deviated_Course_ID")), 
                    solver.mkString(req_course_221)),
                solver.mkTerm(Kind.EQUAL, solver.mkBool(deviation.get("Approved")), solver.mkBool(True))
            )for deviation in transcript.get("Deviations", [])])
        )
    )
    req_course_221_constraint = solver.mkTerm(Kind.AND, solver.mkTerm(Kind.OR, *cs_221_in_transcript), cs_221_approved)
    solver.assertFormula(req_course_221_constraint)
    
    # List of elective courses
    elective_courses = ["CS 223A", "CS 224N", "CS 224S", "CS 224U", "CS 224V", "CS 224W", "CS 228", "CS 229", "CS 231A", "CS 231N", "CS 234", "CS 237A", "CS 237B", "CS 238"]
    elective_vars = [solver.mkConst(solver.getStringSort(), "elective_course_" + str(i)) for i in range(4)]
    elective_constraints = []

    # Check four elective courses in transcript
    for var in elective_vars:
        elective_in_transcript = [solver.mkTerm(Kind.EQUAL, var, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
        elective_in_list = [solver.mkTerm(Kind.EQUAL, var, solver.mkString(course)) for course in elective_courses]
        elective_constraints.append(solver.mkTerm(Kind.AND, solver.mkTerm(Kind.OR, *elective_in_transcript), solver.mkTerm(Kind.OR, *elective_in_list)))

    solver.assertFormula(solver.mkTerm(Kind.AND, *elective_constraints))
    
    # List of additional approved courses
    additional_courses = ["CS 205L", "CS 224R", "CS 225A", "CS 227B", "CS 229M", "CS 230", "CS 233", "CS 235", "CS 236", "CS 239", "CS 246", "CS 257", "CS 270", "CS 271", "CS 273A", "CS 273B", "CS 274", "CS 275", "CS 279", "CS 281", "CS 322", "CS 324", "CS 325B", "CS 326", "CS 327A", "CS 329", "CS 330", "CS 331B", "CS 332", "CS 333", "CS 345", "CS 348N", "CS 361", "CS 368", "CS 371", "CS 375", "CS 377", "CS 379", "CS 398", "CS 399", "CS 428A", "CS 428B", "CS 432", "EE 263", "EE 276", "EE 278", "EE 364A", "EE 364B", "EE 377", "EE 378B", "ENGR 205", "ENGR 209A", "MS&E 226", "MS&E 252", "PSYCH 209", "STATS 202", "STATS 315A", "STATS 315B"]

    # Check total units from approved additional courses (must sum to at least 21 units)
    total_units = solver.mkConst(solver.getIntegerSort(), "total_units")
    units_expr = solver.mkInteger(0)
    for course in transcript.get("Courses_Taken", []):
        course_id = course.get("Course_ID")
        earned_units = solver.mkInteger(course.get("Earned_Units"))
        if course_id in additional_courses:
            units_expr = solver.mkTerm(Kind.ADD, units_expr, earned_units)

    unit_constraint = solver.mkTerm(Kind.GEQ, units_expr, solver.mkInteger(21))
    solver.assertFormula(unit_constraint)
    
    # Check courses requiring advisor approval annotated with "†"
    advisor_approved_courses = [course for course in additional_courses if "†" in course]
    approved_courses_vars = [solver.mkConst(solver.getStringSort(), f"approved_course_var_{i}") for i in range(len(advisor_approved_courses))]

    approved_constraints = []
    for i, var in enumerate(approved_courses_vars):
        approval_check = [solver.mkTerm(Kind.EQUAL, var, solver.mkString(course.get("Approved_Course_ID"))) for course in transcript.get("Approval", [])]
        advisor_approved = solver.mkTerm(Kind.AND, solver.mkTerm(Kind.OR, *approval_check), solver.mkTerm(Kind.EQUAL, var, solver.mkString(advisor_approved_courses[i])))
        approved_constraints.append(advisor_approved)

    solver.assertFormula(solver.mkTerm(Kind.AND, *approved_constraints))
    
    # Combine all constraints together
    final_constraints = [req_course_221_constraint] + elective_constraints + [unit_constraint] + approved_constraints
    final_formula = solver.mkTerm(Kind.AND, *final_constraints)
    solver.assertFormula(final_formula)
