
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

def check_transcript_requirements(transcript):
    solver = solver_init()

    # Requirement 1
    course_ids = [
        solver.mkConst(solver.getIntegerSort(), f"course_id_{i}")
        for i, course in enumerate(transcript["Courses_Taken"])
    ]
    constraints_set = [
        solver.mkTerm(Kind.GEQ, course_id, solver.mkInteger(100))
        for course_id in course_ids
    ]
    requirement_1 = solver.mkTerm(Kind.AND, *constraints_set)

    # Requirement 2: At most 10 units of Foundations requirement courses.
    foundations_courses = [
        course for course in transcript["Courses_Taken"]
        if "Foundations" in course["Title"]
    ]
    foundations_units = sum(course["Earned_Units"] for course in foundations_courses)
    requirement_2 = solver.mkTerm(Kind.LEQ, solver.mkInteger(foundations_units), solver.mkInteger(10))

    # Requirement 3: At most 3 units of 1-2 unit seminars.
    seminar_units = sum(
        course["Earned_Units"] for course in transcript["Courses_Taken"]
        if 1 <= course["Earned_Units"] <= 2
    )
    requirement_3 = solver.mkTerm(Kind.LEQ, solver.mkInteger(seminar_units), solver.mkInteger(3))

    # Requirement 4: At least 36 units for a letter grade.
    courses_letter_grade = [
        course for course in transcript["Courses_Taken"]
        if course["Grade"] not in ["CR", "S"]
    ]
    # Add courses satisfying the exception for Spring 19-20 through Summer 20-21
    courses_cr_s_in_exception = []
    for course in transcript["Courses_Taken"]:
        if course["Grade"] in ["CR", "S"] and "Spring_19-20" <= course.get("Term", "") <= "Summer_20-21":
            courses_cr_s_in_exception.append(course)
    letter_grade_units = sum(
        course["Earned_Units"] for course in courses_letter_grade + courses_cr_s_in_exception
    )
    requirement_4 = solver.mkTerm(Kind.GEQ, solver.mkInteger(letter_grade_units), solver.mkInteger(36))

    # Requirement 5: Average grade must be at least 3.0.
    grade_map = {
        "A": 4.0, "A-": 3.7, "B+": 3.3, "B": 3.0, "B-": 2.7, "C+": 2.3,
        "C": 2.0, "C-": 1.7, "D+": 1.3, "D": 1.0, "F": 0.0
    }
    total_units = sum(
        course["Earned_Units"] for course in transcript["Courses_Taken"] if course["Grade"] in grade_map)
    total_points = sum(
        (grade_map[course["Grade"]] * course["Earned_Units"]) for course in transcript["Courses_Taken"] if course["Grade"] in grade_map
    )
    average_gpa = total_points / total_units if total_units > 0 else 0
    requirement_5 = solver.mkTerm(Kind.GEQ, solver.mkReal(average_gpa), solver.mkReal(3.0))

    # Requirement 6: Units applied toward BS may not count toward MSCS.
    bs_units = sum(course["Earned_Units"] for course in transcript["AP_Credits"])
    mscs_units = sum(course["Earned_Units"] for course in transcript["Courses_Taken"])
    requirement_6 = solver.mkTerm(Kind.GT, solver.mkInteger(mscs_units), solver.mkInteger(bs_units))

    # Requirement 7: At least 45 graduate units at Stanford.
    requirement_7 = solver.mkTerm(Kind.GEQ, solver.mkInteger(mscs_units), solver.mkInteger(45))

    # Combine all requirements
    final_formula = solver.mkTerm(Kind.AND, requirement_1, requirement_2, requirement_3, requirement_4, requirement_5, requirement_6, requirement_7)
    solver.assertFormula(final_formula)

    return result_checker(solver, [])

# Test case
if __name__ == "__main__":
    transcript = {
        "Courses_Taken": [
            {"Title": "Core Course", "Earned_Units": 4, "Grade": "A", "Term": "Winter_19-20"},
            {"Title": "Foundations in Computing", "Earned_Units": 5, "Grade": "B+", "Term": "Fall_20-21"},
            {"Title": "Seminar on AI", "Earned_Units": 2, "Grade": "CR", "Term": "Spring_19-20"},
            {"Title": "Advanced Algorithms", "Earned_Units": 3, "Grade": "A-", "Term": "Fall_20-21"}
            # Add more courses as needed for testing
        ],
        "AP_Credits": [
            {"Title": "High School AP", "Earned_Units": 5}
        ]
    }

    check_transcript_requirements(transcript)
