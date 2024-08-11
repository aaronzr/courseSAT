
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

    # Core (15 units minimum): CS107 or 107E, CS111, CS161
    course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
    course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")

    # Constraints for courses taken
    constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    # Core course constraints
    constraints_core_courses = [
        solver.mkTerm(Kind.OR, *constraints_set1),
        solver.mkTerm(Kind.OR, *constraints_set2),
        solver.mkTerm(Kind.OR, 
            solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString('CS107')), 
            solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString('107E'))),
        solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString('CS111')),
        solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString('CS161'))
    ]

    solver.assertFormula(solver.mkTerm(Kind.AND, *constraints_core_courses))

    # Depth; Track and Electives (25 units and seven courses minimum)
    # Track requirements
    constraints_track_a = [
        solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString('CS 112')),
        solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString('140E'))
    ]
    constraint_track_a = solver.mkTerm(Kind.OR, *constraints_track_a)

    constraints_track_b = [
        solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString('CS 143')),
        solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString('EE 180'))
    ]
    constraint_track_b = solver.mkTerm(Kind.OR, *constraints_track_b)

    constraint_track_c = [
        solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course_unit)) for course_unit in [
            'CS 144', 'CS 145', 'CS 149', 'CS 155', 'CS 190', 'CS 217', 
            'CS 240', 'CS 240LX', 'CS 242', 'CS 243', 'CS 244', 'CS 245',
            'EE 271', 'EE 282'
        ]
    ]

    constraint_track_d = [
        solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course_unit)) for course_unit in [
            'CS 144', 'CS 145', 'CS 149', 'CS 155', 'CS 190', 'CS 217', 
            'CS 240', 'CS 240LX', 'CS 242', 'CS 243', 'CS 244', 'CS 245',
            'EE 271', 'EE 282'
        ]
    ]

    constraints_depth = solver.mkTerm(Kind.AND, 
        constraint_track_a, constraint_track_b, 
        solver.mkTerm(Kind.OR, *constraint_track_c), 
        solver.mkTerm(Kind.OR, *constraint_track_d),
        solver.mkTrue()  # Placeholder for additional courses requirement
    )

    solver.assertFormula(constraints_depth)

    # Senior Project (1 course required)
    constraints_senior_project = [
        solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course_unit)) for course_unit in [
            'CS 191', 'CS 191W', 'CS 194', 'CS 194H', 'CS 194W', 'CS 210B', 'CS 294'
        ]
    ]
    constraint_senior_project = solver.mkTerm(Kind.OR, *constraints_senior_project)
    solver.assertFormula(constraint_senior_project)
    
    # Check the result
    variables = [course_variable_1, course_variable_2]
    return result_checker(solver, variables)

def test_function():
    # Example transcript schema for testing
    transcript = {
        "Courses_Taken": [
            {"Course_ID": "CS107"},
            {"Course_ID": "CS111"},
            {"Course_ID": "CS161"},
            {"Course_ID": "CS 112"},
            {"Course_ID": "CS 143"},
            {"Course_ID": "CS 144"},
            {"Course_ID": "CS 145"},
            {"Course_ID": "CS 191"}
        ]
    }
    
    result = function(transcript)
    print("Test result:", result)

if __name__ == "__main__":
    test_function()
