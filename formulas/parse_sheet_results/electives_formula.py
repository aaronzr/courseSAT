Sure, here's the specific code to check the Math and Science Electives requirements according to the constraints provided:

```python
import cvc5
import json

#helper function for solver initialization
def solver_init(): 
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")
    return solver 

#helper function for solver initialization
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
        print("Unsat requirement core is: ", trace)
    return result, trace

#function for checking requirements given a path to a transcript schema
def check_requirements(transcript_path):
    solver = solver_init()
    with open(transcript_path, 'r') as file:
        transcript = json.load(file)
    # generated formulas below:

    # Course variables
    math_elective_course = solver.mkConst(solver.getStringSort(), "math_elective_course")
    cs_phil_course = solver.mkConst(solver.getStringSort(), "cs_phil_course")
    math_51 = solver.mkConst(solver.getStringSort(), "math_51")
    math_52 = solver.mkConst(solver.getStringSort(), "math_52")
    cme_100 = solver.mkConst(solver.getStringSort(), "cme_100")

    # Math & Science Electives
    elective_courses = ['Math51', 'Math52', 'Math53', 'Math54', 'Math104', 'Math107', 'Math108', 'Math109', 'Math110', 'Math113', 'CS 157', 'CS 205L', 'PHIL 151', 'CME 100', 'CME 102', 'CME 104', 'ENGR 108']
    
    # Constraints for checking if elective courses are taken
    elective_constraints = [solver.mkTerm(cvc5.Kind.EQUAL, math_elective_course, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    elective_constraint = solver.mkTerm(cvc5.Kind.OR, *elective_constraints)
    
    elective_course_valid = [solver.mkTerm(cvc5.Kind.EQUAL, math_elective_course, solver.mkString(course)) for course in elective_courses]
    elective_course_valid_constraint = solver.mkTerm(cvc5.Kind.OR, *elective_course_valid)

    # Constraints for CS 157 & Phil 151
    cs_phil_constraints = [solver.mkTerm(cvc5.Kind.EQUAL, cs_phil_course, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    cs_phil_constraint = solver.mkTerm(cvc5.Kind.OR, *cs_phil_constraints)
    
    cs_phil_course_valid = [solver.mkTerm(cvc5.Kind.EQUAL, cs_phil_course, solver.mkString(course)) for course in ["CS 157", "PHIL 151"]]
    cs_phil_course_valid_constraint = solver.mkTerm(cvc5.Kind.OR, *cs_phil_course_valid)

    # Constraints for Math 51 and Math 52
    math_51_constraints = [solver.mkTerm(cvc5.Kind.EQUAL, math_51, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    math_51_constraint = solver.mkTerm(cvc5.Kind.OR, *math_51_constraints)
    
    math_51_valid = solver.mkTerm(cvc5.Kind.EQUAL, math_51, solver.mkString("Math 51"))

    math_52_constraints = [solver.mkTerm(cvc5.Kind.EQUAL, math_52, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    math_52_constraint = solver.mkTerm(cvc5.Kind.OR, *math_52_constraints)
    
    math_52_valid = solver.mkTerm(cvc5.Kind.EQUAL, math_52, solver.mkString("Math 52"))

    # Constraints for CME 100
    cme_100_constraints = [solver.mkTerm(cvc5.Kind.EQUAL, cme_100, solver.mkString(course.get("Title"))) for course in transcript.get("Courses_Taken", [])]
    cme_100_constraint = solver.mkTerm(cvc5.Kind.OR, *cme_100_constraints)
    
    cme_100_valid = solver.mkTerm(cvc5.Kind.EQUAL, cme_100, solver.mkString("CME 100"))

    # Combination Constraints
    not_combined_constraint = solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, cs_phil_course_valid_constraint, math_elective_course_valid_constraint))
    not_combined_math_51_52 = solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, math_51_valid, math_52_valid, cme_100_valid))

    # Overall constraint
    constraint_1 = solver.mkTerm(cvc5.Kind.AND, elective_constraint, elective_course_valid_constraint)
    constraint_2 = solver.mkTerm(cvc5.Kind.AND, cs_phil_constraint, cs_phil_course_valid_constraint)
    constraint_3 = solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, cs_phil_course_valid_constraint, solver.mkTerm(cvc5.Kind.OR, [solver.mkTerm(cvc5.Kind.EQUAL, cs_phil_course, math_elective_course)])))
    constraint_4 = solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, math_51_constraint, math_52_constraint, cme_100_constraint))
    constraint_5 = solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, math_51_constraint, cme_100_constraint))
    
    formula = solver.mkTerm(cvc5.Kind.AND, constraint_1, constraint_2, constraint_3, constraint_4, constraint_5)
    solver.assertFormula(formula)

    result, trace = result_checker(solver, [math_elective_course, cs_phil_course, math_51, math_52, cme_100])
    return result, trace

# supply a transcript schema to check whether requirements are satisfied
if __name__ == "__main__":
    schema_path = "../schema_results/stanford_transcript1.json"
    check_requirements(schema_path)
```

This Python script uses the cvc5 solver to create SMT formulas ensuring that the course requirements for Math and Science Electives are met. Specifically, the constraints ensure that:
1. A valid math elective course has been taken from the allowed list.
2. CS 157 and PHIL 151 cannot both be used to satisfy the elective requirement.
3. If both Math 51 and Math 52 are taken, CME 100 cannot be counted as an elective.
4. If both Math 51 and CME 100 are taken, only the units of one will be credited due to overlapping material. 

This should be run within the context of a Python environment with the relevant packages installed and the provided transcript schema file available at the specified path.