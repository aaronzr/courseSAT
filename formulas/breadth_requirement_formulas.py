
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
    
    # Create course variables for the three breadth requirements
    course_a = solver.mkConst(solver.getStringSort(), "course_a")
    course_b = solver.mkConst(solver.getStringSort(), "course_b")
    course_c = solver.mkConst(solver.getStringSort(), "course_c")

    # Check that the courses are unique and from different areas
    constraints_set1 = []
    constraints_set2 = []
    constraints_set3 = []

    for course in transcript.get("Courses_Taken", []):
        constraints_set1.append(solver.mkTerm(Kind.EQUAL, course_a, solver.mkString(course.get("Course_ID"))))
        constraints_set2.append(solver.mkTerm(Kind.EQUAL, course_b, solver.mkString(course.get("Course_ID"))))
        constraints_set3.append(solver.mkTerm(Kind.EQUAL, course_c, solver.mkString(course.get("Course_ID"))))

    constraint1 = solver.mkTerm(Kind.OR, *constraints_set1)
    constraint2 = solver.mkTerm(Kind.OR, *constraints_set2)
    constraint3 = solver.mkTerm(Kind.OR, *constraints_set3)

    # Constraint for at least 3 units per course
    units_constraints = []
    for course in transcript.get("Courses_Taken", []):
        if course["Earned_Units"] >= 3:
            units_constraints.append(solver.mkTrue())
        else:
            units_constraints.append(solver.mkFalse())
    
    units_constraints_combined = solver.mkTerm(Kind.AND, *units_constraints)

    # Constraint for letter grade
    grade_constraints = []
    letters = ["A", "B", "C", "D", "F"]
    for course in transcript.get("Courses_Taken", []):
        if course["Grade"] in letters:
            grade_constraints.append(solver.mkTrue())
        else:
            grade_constraints.append(solver.mkFalse())

    grade_constraints_combined = solver.mkTerm(Kind.AND, *grade_constraints)

    # Constraints for courses from different areas
    area_a_courses = ["CS 154", "CS 157", "CS 168", "CS 254", "CS 261", "CS 265", "EE 364A", "EE 364B", "Phil 251"]
    area_b_courses = ["CS 140", "CS 140E", "CS 143", "CS 144", "CS 149", "CS 212", "CS 242", "CS 243", "CS 244", "CS 244B", "CS 295", "CS 316", "CS 358", "EE 180", "EE 282", "EE 382E"]
    area_c_courses = ["CS 145", "CS 147", "CS 148", "CS 155", "CS 173", "CS 221", "CS 223A", "CS 224N", "CS 224U", "CS 224W", "CS 227B", "CS 228", "CS 229", "CS 229M", "CS 231A", "CS 231N", "CS 234", "CS 236", "CS 237A", "CS 245", "CS 246", "CS 247", "CS 248", "CS 248A", "CS 251", "CS 255", "CS 273A", "CS 273B", "CS 279", "CS 345", "CS 347", "CS 348A", "CS 348B", "CS 348C", "CS 348E", "CS 348I", "CS 348K", "CS 355", "CS 356", "CS 373"]
    area_d_courses = ["CS 152", "CS 181", "CS 182", "CS 256", "CS 281", "CS 329T", "CS 384", "AMSTUD 133", "AMSTUD 145", "ANTHRO 132D", "COMM 118S", "COMM 120W", "COMM 124", "COMM 130D", "COMM 145", "COMM 154", "COMM 166", "COMM 186W", "COMM 230A", "COMM 230B", "COMM 230C", "DESINST 215", "DESINST 240", "EARTHSYS 213", "ENGLISH 184D", "ENGR 248", "HISTORY 244F", "INTLPOL 268", "LAW 4039", "ME 177", "MS&E 193", "MS&E 231", "MS&E 234", "MS&E 254", "POLISCI 150A", "PSYCH 215", "PUBLPOL 103F", "PUBLPOL 353B"]

    constraints_set_a = [solver.mkTerm(Kind.EQUAL, course_a, solver.mkString(course)) for course in area_a_courses]
    constraints_set_b = [solver.mkTerm(Kind.EQUAL, course_b, solver.mkString(course)) for course in area_b_courses]
    constraints_set_c = [solver.mkTerm(Kind.EQUAL, course_c, solver.mkString(course)) for course in area_c_courses]

    constraint_area_a = solver.mkTerm(Kind.OR, *constraints_set_a)
    constraint_area_b = solver.mkTerm(Kind.OR, *constraints_set_b)
    constraint_area_c = solver.mkTerm(Kind.OR, *constraints_set_c)

    # Combine all the constraints
    formula = solver.mkTerm(
        Kind.AND,
        constraint1,
        constraint2,
        constraint3,
        units_constraints_combined,
        grade_constraints_combined,
        solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_a, course_b)),  # courses must be different
        solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_a, course_c)),
        solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_b, course_c)),
        solver.mkTerm(Kind.OR, constraint_area_a, constraint_area_b, constraint_area_c)
    )

    solver.assertFormula(formula)
    
    result_checker(solver, [course_a, course_b, course_c])


# Simple test case
test_transcript = {
    "Courses_Taken": [
        {"Course_ID": "CS 140", "Earned_Units": 4, "Grade": "A"},
        {"Course_ID": "CS 154", "Earned_Units": 4, "Grade": "B"},
        {"Course_ID": "CS 147", "Earned_Units": 3, "Grade": "C"},
    ]
}

function(test_transcript)
