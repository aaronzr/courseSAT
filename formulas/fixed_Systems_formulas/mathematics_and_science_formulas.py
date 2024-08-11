
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
    
    # Helper function to create a constraint
    def create_constraint(kind, variable, course_list):
        constraints = [
            solver.mkTerm(Kind.EQUAL, variable, solver.mkString(course.get("Course_ID"))) 
            for course in course_list
        ]
        if len(constraints) == 0:
            return solver.mkBoolean(False)
        elif len(constraints) == 1:
            return constraints[0]
        else:
            return solver.mkTerm(kind, *constraints)

    courses = transcript.get("Courses_Taken", [])
    
    # MATH19 Calculus constraint
    math19_variable = solver.mkConst(solver.getStringSort(), "MATH19")
    constraint_math19 = create_constraint(Kind.OR, math19_variable, [course for course in courses if course.get("Title") == "MATH19 Calculus"])
    solver.assertFormula(constraint_math19)
    
    # MATH20 constraint
    math20_variable = solver.mkConst(solver.getStringSort(), "MATH20")
    constraint_math20 = create_constraint(Kind.OR, math20_variable, [course for course in courses if course.get("Title") == "MATH20"])
    solver.assertFormula(constraint_math20)
    
    # MATH21 constraint
    math21_variable = solver.mkConst(solver.getStringSort(), "MATH21")
    constraint_math21 = create_constraint(Kind.OR, math21_variable, [course for course in courses if course.get("Title") == "MATH21"])
    solver.assertFormula(constraint_math21)
    
    # CS103 Mathematical Foundations of Computing constraint
    cs103_variable = solver.mkConst(solver.getStringSort(), "CS103")
    constraint_cs103 = create_constraint(Kind.OR, cs103_variable, [course for course in courses if course.get("Title") == "CS103 Mathematical Foundations of Computing"])
    solver.assertFormula(constraint_cs103)
    
    # CS109 Introduction to Probability for Computer Scientists constraint
    cs109_variable = solver.mkConst(solver.getStringSort(), "CS109")
    constraint_cs109 = create_constraint(Kind.OR, cs109_variable, [course for course in courses if course.get("Title") == "CS109 Introduction to Probability for Computer Scientists"])
    solver.assertFormula(constraint_cs109)
    
    # PHYS41 Mechanics (or PHYS 21 or 61) constraint
    phys41_variable = solver.mkConst(solver.getStringSort(), "PHYS41")
    constraint_phys41 = create_constraint(Kind.OR, phys41_variable, [course for course in courses if course.get("Title") in ["PHYS41 Mechanics", "PHYS 21", "PHYS 61"]])
    solver.assertFormula(constraint_phys41)
    
    # PHYS43 Electricity and Magnetism (or PHYS 23 or PHYS 81/63) constraint
    phys43_variable = solver.mkConst(solver.getStringSort(), "PHYS43")
    constraint_phys43 = create_constraint(Kind.OR, phys43_variable, [course for course in courses if course.get("Title") in ["PHYS43 Electricity and Magnetism", "PHYS 23", "PHYS 81", "PHYS 63"]])
    solver.assertFormula(constraint_phys43)
    
    variables = [math19_variable, math20_variable, math21_variable, cs103_variable, cs109_variable, phys41_variable, phys43_variable]
    result_checker(solver, variables)

# Test case to verify the correctness
if __name__ == "__main__":
    test_transcript = {
        "Courses_Taken": [
            {"Course_ID": "MATH19_001", "Title": "MATH19 Calculus"},
            {"Course_ID": "MATH20_001", "Title": "MATH20"},
            {"Course_ID": "MATH21_001", "Title": "MATH21"},
            {"Course_ID": "CS103_001", "Title": "CS103 Mathematical Foundations of Computing"},
            {"Course_ID": "CS109_001", "Title": "CS109 Introduction to Probability for Computer Scientists"},
            {"Course_ID": "PHYS41_001", "Title": "PHYS41 Mechanics"},
            {"Course_ID": "PHYS43_001", "Title": "PHYS43 Electricity and Magnetism"}
        ]
    }

    function(test_transcript)
