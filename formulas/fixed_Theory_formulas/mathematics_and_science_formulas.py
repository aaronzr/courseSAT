
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
                print(f"Model for {variable}: {model}")
    else: 
        core = solver.getUnsatCore()
        print("Unsat requirement core is: ", core)
    return result

def function(transcript, Math_electives_list, Math_courses_list, Science_electives_list, Science_courses_list):
    solver = solver_init()

    # Helper to convert earned units to terms
    def convert_units_to_term(units_str):
        try:
            return solver.mkReal(units_str)
        except Exception as e:
            print(f"Error converting units: {units_str} -> {e}")
            return None

    # Mathematics Requirements:
    # 1. MATH19 Calculus:
    math19_variable = solver.mkConst(solver.getStringSort(), "MATH19")
    constraints_math19 = [solver.mkTerm(Kind.EQUAL, math19_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math19 = solver.mkTerm(Kind.OR, *constraints_math19)
    solver.assertFormula(constraint_math19)

    # 2. MATH20:
    math20_variable = solver.mkConst(solver.getStringSort(), "MATH20")
    constraints_math20 = [solver.mkTerm(Kind.EQUAL, math20_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math20 = solver.mkTerm(Kind.OR, *constraints_math20)
    solver.assertFormula(constraint_math20)

    # 3. MATH21:
    math21_variable = solver.mkConst(solver.getStringSort(), "MATH21")
    constraints_math21 = [solver.mkTerm(Kind.EQUAL, math21_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_math21 = solver.mkTerm(Kind.OR, *constraints_math21)
    solver.assertFormula(constraint_math21)

    # 4. CS103 Mathematical Foundations of Computing:
    cs103_variable = solver.mkConst(solver.getStringSort(), "CS103")
    constraints_cs103 = [solver.mkTerm(Kind.EQUAL, cs103_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs103 = solver.mkTerm(Kind.OR, *constraints_cs103)
    solver.assertFormula(constraint_cs103)

    # 5. CS109 Introduction to Probability for Computer Scientists:
    cs109_variable = solver.mkConst(solver.getStringSort(), "CS109")
    constraints_cs109 = [solver.mkTerm(Kind.EQUAL, cs109_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_cs109 = solver.mkTerm(Kind.OR, *constraints_cs109)
    solver.assertFormula(constraint_cs109)

    # 6. Two electives from Math electives list:
    math_electives = [course.get("Title") for course in transcript.get("Courses_Taken", []) if course.get("Title") in Math_electives_list]
    constraint_math_electives = solver.mkTerm(Kind.GEQ, solver.mkInteger(len(math_electives)), solver.mkInteger(2))
    solver.assertFormula(constraint_math_electives)

    # 7. Total of 26 units minimum:
    math_units_taken = [
        convert_units_to_term(course.get("Earned_Units")) 
        for course in transcript.get("Courses_Taken", []) 
        if course.get("Title") in Math_courses_list
    ]
    math_units_taken = [u for u in math_units_taken if u is not None] # Filter out None values
    if len(math_units_taken) > 0:
        total_math_units = solver.mkTerm(Kind.ADD, *math_units_taken)
    else:
        total_math_units = solver.mkInteger(0) # If no courses are found, set total to 0
    constraint_math_units = solver.mkTerm(Kind.GEQ, total_math_units, solver.mkInteger(26))
    solver.assertFormula(constraint_math_units)

    # Science Requirements:
    # 1. PHYS41 Mechanics (or PHYS 21 or PHYS 61):
    physics_variable = solver.mkConst(solver.getStringSort(), "PHYS41")
    constraints_physics = [solver.mkTerm(Kind.EQUAL, physics_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics = solver.mkTerm(Kind.OR, *constraints_physics)
    solver.assertFormula(constraint_physics)

    # 2. PHYS43 Electricity and Magnetism (or PHYS 23 or PHYS 81/63):
    physics_em_variable = solver.mkConst(solver.getStringSort(), "PHYS43")
    constraints_physics_em = [solver.mkTerm(Kind.EQUAL, physics_em_variable, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    constraint_physics_em = solver.mkTerm(Kind.OR, *constraints_physics_em)
    solver.assertFormula(constraint_physics_em)

    # 3. One elective from the Science List or AP Chemistry:
    science_electives = [course.get("Title") for course in transcript.get("Courses_Taken", []) if course.get("Title") in Science_electives_list or course.get("Title") == "AP Chemistry"]
    constraint_science_electives = solver.mkTerm(Kind.GEQ, solver.mkInteger(len(science_electives)), solver.mkInteger(1))
    solver.assertFormula(constraint_science_electives)

    # 4. Total of 11 units minimum:
    science_units_taken = [
        convert_units_to_term(course.get("Earned_Units")) 
        for course in transcript.get("Courses_Taken", []) 
        if course.get("Title") in Science_courses_list
    ]
    science_units_taken = [u for u in science_units_taken if u is not None] # Filter out None values
    if len(science_units_taken) > 0:
        total_science_units = solver.mkTerm(Kind.ADD, *science_units_taken)
    else:
        total_science_units = solver.mkInteger(0)# If no courses are found, set total to 0
    constraint_science_units = solver.mkTerm(Kind.GEQ, total_science_units, solver.mkInteger(11))
    solver.assertFormula(constraint_science_units)

    # Advisor Approval:
    for deviation in transcript.get("Deviations", []):
        if not deviation.get("Approved"):
            deviation_variable = solver.mkConst(solver.getStringSort(), deviation.get("Deviated_Course_ID"))
            constraint_deviation = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, deviation_variable, solver.mkString("None")))
            solver.assertFormula(constraint_deviation)
    for approval in transcript.get("Approval", []):
        if not approval.get("Approved"):
            approval_variable = solver.mkConst(solver.getStringSort(), approval.get("Approved_Course_ID"))
            constraint_approval = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, approval_variable, solver.mkString("None")))
            solver.assertFormula(constraint_approval)
    
    # Check and print results
    result_checker(solver, [])
    return

# Define main for testing
if __name__ == "__main__":
    # Sample transcript for testing
    transcript = {
        "Courses_Taken": [
            {"Title": "MATH19", "Earned_Units": "5"},
            {"Title": "MATH20", "Earned_Units": "5"},
            {"Title": "MATH21", "Earned_Units": "5"},
            {"Title": "CS103", "Earned_Units": "5"},
            {"Title": "CS109", "Earned_Units": "5"},
            {"Title": "PHYS41", "Earned_Units": "5"},
            {"Title": "PHYS43", "Earned_Units": "5"},
            {"Title": "Science Elective", "Earned_Units": "5"},
        ],
        "Deviations": [
            {"Deviated_Course_ID": "None", "Approved": True},
        ],
        "Approval": [
            {"Approved_Course_ID": "None", "Approved": True},
        ]
    }
    Math_electives_list = ["Math Elective 1", "Math Elective 2"]
    Math_courses_list = ["MATH19", "MATH20", "MATH21", "CS103", "CS109"]
    Science_electives_list = ["Science Elective"]
    Science_courses_list = ["PHYS41", "PHYS43", "Science Elective"]

    function(transcript, Math_electives_list, Math_courses_list, Science_electives_list, Science_courses_list)
