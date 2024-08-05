
import os
import sys
import cvc5
import json
from cvc5 import Kind

# Initialize the solver with required options
def solver_init():
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver

# Function to check the result and print relevant information
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

# Function to generate cvc5 solver formulas for Technology in Society Requirement
def function(transcript):
    solver = solver_init()

    # Instantiate course variables
    course_variable = solver.mkConst(solver.getStringSort(), "tis_course")

    # Course is in transcript[*].course
    constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    if constraints_set:
        course_constraint = solver.mkTerm(Kind.OR, *constraints_set)
    else:
        course_constraint = solver.mkBoolean(False)  # No courses taken

    # Course is in the Approved TiS list
    approved_tis_courses = ['Course1', 'Course2', 'Course3']  # list of Approved TiS courses
    tis_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course)) for course in approved_tis_courses]
    tis_constraint = solver.mkTerm(Kind.OR, *tis_constraints)

    # Transfer and AP credits in Math, Science, Fundamentals, & TIS must be approved by the SoE Dean's Office
    approval_constraints = []
    for credit_type in ['Math', 'Science', 'Fundamentals', 'TIS']:
        approved = solver.mkConst(solver.getBooleanSort(), credit_type + "_approved")
        approval_constraints.append(solver.mkTerm(Kind.EQUAL, approved, solver.mkBoolean(True)))

    # Courses listed on this form must be taken for a letter grade
    letter_grade_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course.get("Grade"))) for course in transcript.get("Courses_Taken", [])]

    # Advisor approval constraints
    advisor_approval = solver.mkConst(solver.getBooleanSort(), "advisor_approval")
    advisor_constraint = solver.mkTerm(Kind.EQUAL, advisor_approval, solver.mkBoolean(transcript.get("Approval", {}).get("Approved_By") is not None))

    # Deviation constraints
    deviation_constraints = []
    for deviation in transcript.get("Deviations", []):
        deviated_course_variable = solver.mkConst(solver.getStringSort(), "deviated_course")
        deviation_constraint = solver.mkTerm(Kind.EQUAL, deviated_course_variable, solver.mkString(deviation.get("Deviated_Course_ID")))
        deviation_constraints.append(deviation_constraint)
        deviation_approval = solver.mkConst(solver.getBooleanSort(), "deviation_approval")
        deviation_approval_constraint = solver.mkTerm(Kind.EQUAL, deviation_approval, solver.mkBoolean(deviation.get("Approved_By") is not None))
        deviation_constraints.append(deviation_approval_constraint)

    # Combine all constraints
    constraints = [course_constraint, tis_constraint, *approval_constraints, *letter_grade_constraints, advisor_constraint, *deviation_constraints]

    # Verify that all constraints are Boolean terms
    for i, constraint in enumerate(constraints):
        if constraint.getSort().isBoolean():
            print(f"Constraint {i} is a valid Boolean term.")
        else:
            raise RuntimeError(f"Constraint {i} is not a Boolean term: {constraint}")

    # Create the final formula
    formula = solver.mkTerm(Kind.AND, *constraints)

    # Assert the formula
    solver.assertFormula(formula)

    # Check and print the result
    result_checker(solver, [course_variable, advisor_approval])

# Test case with a sample transcript
def test_function():
    sample_transcript = {
        "Courses_Taken": [
            {"Course_ID": "Course1", "Program_Units": "3", "Grade": "A"},
            {"Course_ID": "Course2", "Program_Units": "3", "Grade": "B"},
        ],
        "Approval": {
            "Approved_By": "advisor_1"
        },
        "Deviations": [
            {"Deviated_Course_ID": "Course3", "Approved_By": "advisor_2"}
        ]
    }
    function(sample_transcript)

# Run the test case
test_function()
