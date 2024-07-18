
import os
import sys
import cvc5
import json
from cvc5 import Kind

# Initialize the solver
def solver_init(): 
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver 

# Check the result of the solver
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
    
    # Function to create the constraints for required courses
    def create_course_constraints(course_ids, course_variable_name):
        course_variable = solver.mkConst(solver.getStringSort(), course_variable_name)
        constraints_set = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(str(course_id))) for course_id in course_ids]
        
        # If only one constraint, return it directly
        if len(constraints_set) == 1:
            return constraints_set[0], course_variable
        return solver.mkTerm(Kind.OR, *constraints_set), course_variable

    # Constraint 1: Logic, Automata & Complexity (CS103)
    course_ids_logic = [103]  # CS103
    constraint_logic, course_variable_logic = create_course_constraints(course_ids_logic, "course_logic")

    # Constraint 2: Probability (CS109, Stat116, CME106, MS&E220, or EE178)
    course_ids_probability = [109, 116, 106, 220, 178]  # CS109, Stat116, CME106, MS&E220, or EE178
    constraint_probability, course_variable_probability = create_course_constraints(course_ids_probability, "course_probability")

    # Constraint 3: Algorithmic Analysis (CS161)
    course_ids_algorithm = [161]  # CS161
    constraint_algorithm, course_variable_algorithm = create_course_constraints(course_ids_algorithm, "course_algorithm")

    # Constraint 4: Computer Organization & Systems (CS107 or CS107E)
    course_ids_computer_org = ['107', '107E']  # CS107 or 107E
    constraint_computer_org, course_variable_computer_org = create_course_constraints(course_ids_computer_org, "course_computer_org")

    # Constraint 5: Principles of Computer Systems (CS110 or CS111)
    course_ids_principles = [110, 111]  # CS110 or CS111
    constraint_principles, course_variable_principles = create_course_constraints(course_ids_principles, "course_principles")

    # Constraint 6: Total Units must not exceed 10
    total_units = sum(course.get("Earned_Units", 0) for course in transcript["Courses_Taken"])
    constraint_units = solver.mkTerm(Kind.LEQ, solver.mkInteger(total_units), solver.mkInteger(10))

    # Combine all constraints
    final_constraints = [
        constraint_logic,
        constraint_probability,
        constraint_algorithm,
        constraint_computer_org,
        constraint_principles,
        constraint_units
    ]
    final_formula = solver.mkTerm(Kind.AND, *final_constraints)

    # Add advisor approval constraints for deviations
    for deviation in transcript["Deviations"]:
        if deviation["Approved"]:
            deviation_approved = deviation["Approved"]
            deviation_course_id = deviation["Deviated_Course_ID"]
            approved_by = deviation["Approved_By"]
            
            deviation_constraint = solver.mkTerm(Kind.AND,
                                                 solver.mkTerm(Kind.EQUAL, solver.mkString(deviation_course_id), solver.mkString(deviation["Deviated_Course_ID"])),
                                                 solver.mkTerm(Kind.EQUAL, solver.mkBoolean(deviation_approved), solver.mkBoolean(True)),
                                                 solver.mkTerm(Kind.EQUAL, solver.mkString(approved_by), solver.mkString(deviation["Approved_By"]))
                                                )
            final_formula = solver.mkTerm(Kind.AND, final_formula, deviation_constraint)

    # Assert the final formula
    solver.assertFormula(final_formula)

    # Check satisfiability
    result = result_checker(solver, [course_variable_logic, course_variable_probability, course_variable_algorithm, course_variable_computer_org, course_variable_principles])
    return result

# Test Code
if __name__ == "__main__":
    transcript = {
        "Student": {
            "Name": "John Doe",
            "Program": "MS Computer Science",
            "StudentID": 123456,
            "Coterm": False
        },
        "AP_Credits": [
            {"Advanced_Placement": "AP Calculus", "Earned_Units": 5}
        ],
        "Courses_Taken": [
            {"Course_ID": 103, "Title": "Logic, Automata & Complexity", "Earned_Units": 3, "Grade": "A"},
            {"Course_ID": 109, "Title": "Probability", "Earned_Units": 3, "Grade": "B+"},
            {"Course_ID": 161, "Title": "Algorithmic Analysis", "Earned_Units": 3, "Grade": "A-"},
            {"Course_ID": 107, "Title": "Computer Organization and Systems", "Earned_Units": 3, "Grade": "B-"},
            {"Course_ID": 110, "Title": "Principles of Computer Systems", "Earned_Units": 3, "Grade": "A-"}
        ],
        "Deviations": [
            {"Deviated_Course_ID": "XX105", "Approved": True, "Approved_By": "Advisor Name"}
        ],
        "Approval": [
            {"Approved": True, "Approved_By": "Advisor Name", "Approved_Course_ID": "XX105"}
        ],
        "Cumulative_GPA": {
            "Undergrad": 3.6,
            "Graduate": 3.8
        }
    }
    
    function(transcript)
