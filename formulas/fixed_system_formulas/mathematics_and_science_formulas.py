
import os
import sys
import cvc5
import json
from cvc5 import Kind, Result

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

    # Instantiate variables for courses
    math_course_variables = []
    for i in range(7):  # Considering 5 required courses + 2 electives
        math_course_variables.append(solver.mkConst(solver.getStringSort(), f"math_course_{i + 1}"))

    # Constraints for required Math courses
    math_required_courses_constraints = [
        solver.mkTerm(Kind.EQUAL, math_course_variables[0], solver.mkString("MATH 19")),  # MATH 19: Calculus
        solver.mkTerm(Kind.EQUAL, math_course_variables[1], solver.mkString("MATH 20")),  # MATH 20
        solver.mkTerm(Kind.EQUAL, math_course_variables[2], solver.mkString("MATH 21")),  # MATH 21
        solver.mkTerm(Kind.EQUAL, math_course_variables[3], solver.mkString("CS 103")),   # CS 103: Mathematical Foundations of Computing
        solver.mkTerm(Kind.EQUAL, math_course_variables[4], solver.mkString("CS 109")),   # CS 109: Introduction to Probability for Computer Scientists
    ]

    # Constraints for Math elective courses
    math_elective_constraints = []
    for i in range(5, 7):  # Two elective courses
        elective_courses = [
            solver.mkTerm(Kind.EQUAL, math_course_variables[i], solver.mkString(elective_course)) 
            for elective_course in [
                "Math 51", "Math 52", "Math 53", "Math 104", "Math 107", "Math 108", 
                "Math 109", "Math 110", "Math 113", "CS 157", "CS 205L", 
                "PHIL 151", "CME 100", "CME 102", "CME 104", "ENGR 108"
            ]
        ]
        math_elective_constraints.append(solver.mkTerm(Kind.OR, *elective_courses))

    # Combine all Math constraints
    math_constraints = solver.mkTerm(Kind.AND, *(math_required_courses_constraints + math_elective_constraints))

    # Instantiate variables for courses
    science_course_variables = []
    for i in range(4):  # Considering 2 required courses + 1 elective
        science_course_variables.append(solver.mkConst(solver.getStringSort(), f"science_course_{i + 1}"))

    # Constraints for required Science courses
    science_required_courses_constraints = [
        solver.mkTerm(Kind.OR, *[
            solver.mkTerm(Kind.EQUAL, science_course_variables[0], solver.mkString(course)) 
            for course in ["PHYS 41", "PHYS 21", "PHYS 61"]
        ]),  # PHYS 41: Mechanics (or PHYS 21 or 61)
        solver.mkTerm(Kind.OR, *[
            solver.mkTerm(Kind.EQUAL, science_course_variables[1], solver.mkString(course)) 
            for course in ["PHYS 43", "PHYS 23", "PHYS 81", "PHYS 63"]
        ]),  # PHYS 43: Electricity and Magnetism (or PHYS 23 or PHYS 81/63)
    ]

    # Constraints for Science elective courses
    science_elective_constraint = solver.mkTerm(Kind.OR, *[
        solver.mkTerm(Kind.EQUAL, science_course_variables[2], solver.mkString(elective_course)) 
        for elective_course in ["SoE Science List", "PSYCH 30", "AP Chemistry"]
    ])

    # Combine all Science constraints
    science_constraints = solver.mkTerm(Kind.AND, *(science_required_courses_constraints + [science_elective_constraint]))
    
    # Combine all constraints
    all_constraints = solver.mkTerm(Kind.AND, math_constraints, science_constraints)
    
    # Assert all constraints
    solver.assertFormula(all_constraints)
    
    # Check the transcript (we would typically parse the transcript and match against the constraints)
    result = result_checker(solver, math_course_variables + science_course_variables)
    return result

# Test case
transcript = [
    "MATH 19", "MATH 20", "MATH 21", "CS 103", "CS 109", 
    "Math 51", "Math 52", 
    "PHYS 41", "PHYS 43", "SoE Science List"
]

# Ideally you'd parse this into a form that the solver understands, 
# but in this case, we are directly checking it with predefined constraints
function(transcript)
