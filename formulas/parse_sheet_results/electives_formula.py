Certainly! I'll follow the instructions and provide the parameterized SMT Python solver formulas for the given constraints.

```python
import json
import cvc5
from cvc5 import Kind

# Helper function for solver initialization
def solver_init():
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver

# Helper function to check results
def result_checker(solver, variables):
    result = solver.checkSat()
    trace = ""
    print("Satisfiability:", result)
    if result.isSat():
        print("SAT")
        if variables:
            for variable in variables:
                trace = solver.getValue(variable)
                print(f"Model for {variable}:", trace)
    else:
        trace = solver.getUnsatCore()
        print("Unsat requirement core is:", trace)
    return result, trace

# Function for checking requirements given a path to a transcript schema
def check_requirements(transcript_path):
    solver = solver_init()
    with open(transcript_path, 'r') as file:
        transcript = json.load(file)
    
    # List of Math and Science elective courses
    elective_courses = ['Math 51', 'Math 52', 'Math 53', 'Math 54', 'Math 104', 'Math 107', 'Math 108', 'Math 109', 'Math 110', 'Math 113',
                        'CS 157', 'CS 205L', 'PHIL 151', 'CME 100', 'CME 102', 'CME 104', 'ENGR 108']

    # Course variables
    courses_taken = {course["Course_ID"]: course["Title"] for course in transcript.get("Courses_Taken", [])}
    
    math51 = solver.mkConst(solver.getStringSort(), "Math51")
    math52 = solver.mkConst(solver.getStringSort(), "Math52")
    math100 = solver.mkConst(solver.getStringSort(), "CME100")
    cs157 = solver.mkConst(solver.getStringSort(), "CS157")
    phil151 = solver.mkConst(solver.getStringSort(), "Phil151")

    # Helper function to create constraints for courses taken
    def create_constraints(course_var, course_title):
        constraints = [solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(courses_taken.get(course_id))) 
                       for course_id, title in courses_taken.items() if title == course_title]
        return solver.mkTerm(Kind.OR, *constraints) if constraints else solver.mkFalse()

    # Constraints for individual courses
    constraint_math51 = create_constraints(math51, "Math 51")
    constraint_math52 = create_constraints(math52, "Math 52")
    constraint_math100 = create_constraints(math100, "CME 100")
    constraint_cs157 = create_constraints(cs157, "CS 157")
    constraint_phil151 = create_constraints(phil151, "PHIL 151")
    
    # Combined constraints for electives with specific exclusion rules:
    # CS 157 + Phil 151 may not be combined
    exclusion_cs157_phil151 = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.AND, constraint_cs157, constraint_phil151))
    
    # Students taking both Math 51 & 52 may not count CME 100 as an elective
    exclusion_math51_52_cme100 = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.AND, constraint_math51, constraint_math52, constraint_math100))
    
    # Students who take both Math 51 & CME 100 will receive only 8 units credit in the major
    unit_violations = solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.AND, constraint_math51, constraint_math100))  # Assume "units credit in major" is handled separately

    # Ensure at least one of the elective courses is taken, following the exclusion rules
    electives_constraints = [create_constraints(solver.mkConst(solver.getStringSort(), f"elective_{i}"), course) for i, course in enumerate(elective_courses)]
    at_least_one_elective = solver.mkTerm(Kind.OR, *electives_constraints) if electives_constraints else solver.mkFalse()

    # Final formula including all constraints
    formula = solver.mkTerm(Kind.AND, at_least_one_elective, exclusion_cs157_phil151, exclusion_math51_52_cme100, unit_violations)
    solver.assertFormula(formula)

    # Check result and print out the evaluation
    result_checker(solver, [math51, math52, math100, cs157, phil151])

# Supply a transcript schema to check whether requirements are satisfied
if __name__ == "__main__":
    schema_path = "../schema_results/stanford_transcript1.json"
    check_requirements(schema_path)
```

This code should correctly set up the CVC5 SMT solver to check for the given constraints on Math and Science electives. The constraints include:
1. Ensuring at least one elective course is taken from the provided list.
2. Enforcing that CS 157 and Phil 151 cannot both be used to satisfy the requirement.
3. Ensuring that if a student takes both Math 51 and Math 52, they cannot count CME 100 as an elective.
4. Addressing credit limitations if both Math 51 and CME 100 are taken (implementation might need specifics on how unit credits are managed).

Replace `schema_path` with the actual path to your JSON transcript file to run this check.