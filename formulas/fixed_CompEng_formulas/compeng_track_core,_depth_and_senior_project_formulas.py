
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

def generate_core_constraints(transcript):
    solver = solver_init()
    
    core_courses = ['CS107', 'CS107E', 'CS111', 'CS161']
    taken_core_courses = [course.get("Title") for course in transcript.get("Courses_Taken", [])]
    
    core_course_vars = [solver.mkConst(solver.getStringSort(), course) for course in core_courses]

    constraints_set = [solver.mkTerm(Kind.EQUAL, core_course_vars[i], solver.mkString(taken_course)) for i, taken_course in enumerate(taken_core_courses)]
    core_constraint = solver.mkTerm(Kind.OR, *constraints_set)
    
    solver.assertFormula(core_constraint)
    
    return result_checker(solver, core_course_vars)
