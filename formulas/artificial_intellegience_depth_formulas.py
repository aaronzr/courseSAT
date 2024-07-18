
import os
import sys
import json
import cvc5
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

def validate_transcript(transcript):
    solver = solver_init()

    # Extract variables from the schema
    transcript_courses = transcript.get("Courses_Taken", [])
    dev_courses = transcript.get("Deviations", [])
    approved_courses = transcript.get("Approval", [])

    # Variables for constraints
    course_ids = ["CS 221", "CS 223A", "CS 224N", "CS 224S", "CS 224U", "CS 224V", "CS 224W",
                  "CS 228", "CS 229", "CS 231A", "CS 231N", "CS 234", "CS 237A", "CS 237B",
                  "CS 238", "CS 205L", "CS 224R", "CS 225A", "CS 227B", "CS 229M", "CS 230",
                  "CS 233", "CS 235", "CS 236", "CS 239", "CS 246", "CS 257", "CS 270", "CS 271",
                  "CS 273A", "CS 273B", "CS 274", "CS 275", "CS 279", "CS 281", "CS 322", "CS 324",
                  "CS 325B", "CS 326", "CS 327A", "CS 329", "CS 330", "CS 331B", "CS 332", "CS 333",
                  "CS 345", "CS 348N", "CS 361", "CS 368", "CS 371", "CS 375", "CS 377", "CS 379",
                  "CS 398", "CS 399", "CS 428A", "CS 428B", "CS 432", "EE 263", "EE 276", "EE 278",
                  "EE 364A", "EE 364B", "EE 377", "EE 378B", "ENGR 205", "ENGR 209A", "MS&E 226",
                  "MS&E 252", "PSYCH 209", "STATS 202", "STATS 315A", "STATS 315B"]

    # Helper function to create course constraints
    def course_in_transcript(course_id):
        return [solver.mkTerm(Kind.EQUAL, solver.mkString(course_id), solver.mkString(course["Course_ID"])) for course in transcript_courses]

    # Constraints for 3 or more units and letter grade
    min_units_constraint = solver.mkTrue()
    letter_grade_constraint = solver.mkTrue()
    grade_sort = solver.getStringSort()

    for course in transcript_courses:
        min_units_constraint = solver.mkTerm(Kind.AND, min_units_constraint, solver.mkTerm(Kind.GEQ, solver.mkInteger(course["Earned_Units"]), solver.mkInteger(3)))
        grade_const = solver.mkConst(grade_sort, course["Grade"])
        grade_constraint_term = solver.mkTerm(Kind.EQUAL, solver.mkString(course["Grade"]), grade_const)
        letter_grade_constraint = solver.mkTerm(Kind.AND, letter_grade_constraint, grade_constraint_term)

    # Constraints for CS 399 max units
    cs399_units = 0
    for course in transcript_courses:
        if course["Course_ID"] == "CS 399":
            cs399_units += course["Earned_Units"]

    cs399_constraint = solver.mkTerm(Kind.LEQ, solver.mkInteger(cs399_units), solver.mkInteger(6))

    # Constraints for approved deviations (max one)
    approved_deviation_count = sum(1 for dev in dev_courses if dev["Approved"])
    approved_deviation_constraint = solver.mkTerm(Kind.LEQ, solver.mkInteger(approved_deviation_count), solver.mkInteger(1))

    # Constraints for specific courses lists
    cs221_constraint = solver.mkTerm(Kind.OR, *course_in_transcript("CS 221"))
    courses_from_b = ["CS 223A", "CS 224N", "CS 224S", "CS 224U", "CS 224V", "CS 224W", "CS 228", "CS 229", 
                      "CS 231A", "CS 231N", "CS 234", "CS 237A", "CS 237B", "CS 238"]
    b_constraints = [solver.mkTerm(Kind.OR, *course_in_transcript(course_id)) for course_id in courses_from_b]
    
    # Summing constraints manually to replace mkSum
    sum_b_constraints = solver.mkInteger(0)
    for term in b_constraints:
        sum_b_constraints = solver.mkTerm(Kind.ADD, sum_b_constraints, solver.mkTerm(Kind.ITE, term, solver.mkInteger(1), solver.mkInteger(0)))
    
    at_least_four_from_b = solver.mkTerm(Kind.GEQ, sum_b_constraints, solver.mkInteger(4))

    # Constraint for at least 21 units from specified courses
    total_units = solver.mkInteger(0)
    for course in transcript_courses:
        for course_id in course_ids:
            total_units = solver.mkTerm(Kind.ADD, total_units, solver.mkTerm(Kind.ITE, solver.mkTerm(Kind.EQUAL, solver.mkString(course["Course_ID"]), solver.mkString(course_id)), solver.mkInteger(course["Earned_Units"]), solver.mkInteger(0)))

    total_units_constraint = solver.mkTerm(Kind.GEQ, total_units, solver.mkInteger(21))

    # Overall constraint
    final_constraint = solver.mkTerm(Kind.AND, min_units_constraint, 
                                     letter_grade_constraint, 
                                     cs399_constraint,
                                     approved_deviation_constraint, 
                                     cs221_constraint, 
                                     at_least_four_from_b, 
                                     total_units_constraint)

    solver.assertFormula(final_constraint)

    # Check satisfiability
    result = solver.checkSat()
    print("Satisfiable" if result.isSat() else "Unsatisfiable")
    return result

# Sample transcript schema for testing
sample_transcript = {
    "Courses_Taken": [
        {"Course_ID": "CS 221", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": "CS 223A", "Earned_Units": 3, "Grade": "B"},
        {"Course_ID": "CS 224N", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": "CS 224S", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": "CS 224U", "Earned_Units": 3, "Grade": "B"},
        {"Course_ID": "CS 228", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": "CS 399", "Earned_Units": 6, "Grade": "A"},
    ],
    "Deviations": [],
    "Approval": [],
}

# Run the validation check on the sample transcript
validate_transcript(sample_transcript)
