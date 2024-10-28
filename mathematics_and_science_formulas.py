python
import os
import sys
import cvc5
import collections
import json
from cvc5 import Kind

def solver_init():
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver

def generate_mathematics_constraints(solver, transcript):
    math_courses = ["MATH19", "MATH20", "MATH21", "CS103", "CS109"]
    math_electives = ["Math 51", "Math 52", "Math 53", "Math 104", "Math 107", "Math 108", "Math 109", "Math 110", "Math 113", 
                      "CS 157", "CS 205L", "PHIL 151", "CME 100", "CME 102", "CME 104", "ENGR 108"]
    
    math_constraints = []
    for course in transcript.get("Courses_Taken", []):
        if course.get("Title") in math_courses:
            math_constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), solver.mkString("1")))
        elif course.get("Title") in math_electives:
            math_constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), solver.mkString("1")))
    
    # Units constraint for Mathematics
    units_sum = sum([int(course.get("Earned_Units")) for course in transcript.get("Courses_Taken", [])])
    math_units_constraint = solver.mkTerm(Kind.GREATER_EQ, solver.mkReal(str(units_sum)), solver.mkReal("26"))
    
    # At least 2 math electives constraint
    math_electives_taken = [course.get("Title") for course in transcript.get("Courses_Taken", []) if course.get("Title") in math_electives]
    math_electives_count = collections.Counter(math_electives_taken)
    math_electives_count_constraint = solver.mkTerm(Kind.GREATER_EQ, solver.mkReal(str(len(math_electives_count))), solver.mkReal("2"))
    
    return math_constraints, math_units_constraint, math_electives_count_constraint

def generate_science_constraints(solver, transcript):
    science_courses = ["PHYS41", "PHYS21", "PHYS61", "PHYS43", "PHYS23", "PHYS81", "PHYS63"]
    science_electives = ["SoE Science List", "PSYCH 30", "AP Chemistry"]
    
    science_constraints = []
    for course in transcript.get("Courses_Taken", []):
        if course.get("Title") in science_courses:
            science_constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), solver.mkString("1")))
        elif course.get("Title") in science_electives:
            science_constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), solver.mkString("1")))
    
    # Units constraint for Science
    units_sum = sum([int(course.get("Earned_Units")) for course in transcript.get("Courses_Taken", [])])
    science_units_constraint = solver.mkTerm(Kind.GREATER_EQ, solver.mkReal(str(units_sum)), solver.mkReal("11"))
    
    return science_constraints, science_units_constraint

def function(transcript):
    solver = solver_init()
    
    # Generate constraints for Mathematics requirements
    math_constraints, math_units_constraint, math_electives_count_constraint = generate_mathematics_constraints(solver, transcript)
    
    # Add Mathematics constraints to the solver
    for constraint in math_constraints:
        solver.assertFormula(constraint)
    solver.assertFormula(math_units_constraint)
    solver.assertFormula(math_electives_count_constraint)
    
    # Generate constraints for Science requirements
    science_constraints, science_units_constraint = generate_science_constraints(solver, transcript)
    
    # Add Science constraints to the solver
    for constraint in science_constraints:
        solver.assertFormula(constraint)
    solver.assertFormula(science_units_constraint)
    
    # Check result and output
    result_checker(solver, None)

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
        print("Unsat requirement core is:", core)
    return result

# Test case
sample_transcript = {
    "Courses_Taken": [
        {"Title": "MATH19", "Course_ID": "MATH19", "Earned_Units": "5"},
        {"Title": "MATH21", "Course_ID": "MATH21", "Earned_Units": "5"},
        {"Title": "CS103", "Course_ID": "CS103", "Earned_Units": "5"},
        {"Title": "CS109", "Course_ID": "CS109", "Earned_Units": "5"},
        {"Title": "Math 51", "Course_ID": "MATH51", "Earned_Units": "3"},
        {"Title": "Math 52", "Course_ID": "MATH52", "Earned_Units": "3"},
        {"Title": "PHYS41", "Course_ID": "PHYS41", "Earned_Units": "4"},
        {"Title": "PHYS43", "Course_ID": "PHYS43", "Earned_Units": "4"},
        {"Title": "PSYCH 30", "Course_ID": "PSYCH30", "Earned_Units": "3"},
    ]
}

function(sample_transcript)
