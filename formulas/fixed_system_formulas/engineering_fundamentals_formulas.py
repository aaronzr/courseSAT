
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

def check_transcript(transcript):
    solver = solver_init()

    # Mathematics Requirement
    course_variable_calculus = solver.mkConst(solver.getStringSort(), "calculus_course")
    course_variable_cs103 = solver.mkConst(solver.getStringSort(), "cs103_course")
    course_variable_math_elective1 = solver.mkConst(solver.getStringSort(), "math_elective1_course")
    course_variable_math_elective2 = solver.mkConst(solver.getStringSort(), "math_elective2_course")

    constraints_calculus = [solver.mkTerm(Kind.EQUAL, course_variable_calculus,
                                          solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_cs103 = [solver.mkTerm(Kind.EQUAL, course_variable_cs103,
                                       solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_math_elective1 = [solver.mkTerm(Kind.EQUAL, course_variable_math_elective1,
                                                solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_math_elective2 = [solver.mkTerm(Kind.EQUAL, course_variable_math_elective2,
                                                solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    if constraints_calculus:
        constraint_calculus = solver.mkTerm(Kind.OR, *constraints_calculus)
    else:
        constraint_calculus = solver.mkFalse()

    if constraints_cs103:
        constraint_cs103 = solver.mkTerm(Kind.OR, *constraints_cs103)
    else:
        constraint_cs103 = solver.mkFalse()

    if constraints_math_elective1:
        constraint_math_elective1 = solver.mkTerm(Kind.OR, *constraints_math_elective1)
    else:
        constraint_math_elective1 = solver.mkFalse()

    if constraints_math_elective2:
        constraint_math_elective2 = solver.mkTerm(Kind.OR, *constraints_math_elective2)
    else:
        constraint_math_elective2 = solver.mkFalse()

    constraints_set_calculus = [solver.mkTerm(Kind.EQUAL, course_variable_calculus, solver.mkString(course_unit))
                                for course_unit in ['MATH 19', 'MATH 20', 'MATH 21']]
    constraint_calculus_unit = solver.mkTerm(Kind.OR, *constraints_set_calculus)

    formulas_mathematics = solver.mkTerm(Kind.AND, constraint_calculus, constraint_cs103, constraint_math_elective1,
                                         constraint_math_elective2, constraint_calculus_unit)
    solver.assertFormula(formulas_mathematics)

    # Science Requirement
    course_variable_mechanics = solver.mkConst(solver.getStringSort(), "mechanics_course")
    course_variable_electricity_magnetism = solver.mkConst(solver.getStringSort(), "electricity_magnetism_course")

    constraints_mechanics = [solver.mkTerm(Kind.EQUAL, course_variable_mechanics,
                                           solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_electricity_magnetism = [solver.mkTerm(Kind.EQUAL, course_variable_electricity_magnetism,
                                                       solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    if constraints_mechanics:
        constraint_mechanics = solver.mkTerm(Kind.OR, *constraints_mechanics)
    else:
        constraint_mechanics = solver.mkFalse()

    if constraints_electricity_magnetism:
        constraint_electricity_magnetism = solver.mkTerm(Kind.OR, *constraints_electricity_magnetism)
    else:
        constraint_electricity_magnetism = solver.mkFalse()

    constraints_set_mechanics = solver.mkTerm(Kind.EQUAL, course_variable_mechanics, solver.mkString('PHYS 41'))
    constraints_set_electricity_magnetism = solver.mkTerm(Kind.EQUAL, course_variable_electricity_magnetism, solver.mkString('PHYS 43'))

    formulas_science = solver.mkTerm(Kind.AND, constraint_mechanics, constraint_electricity_magnetism,
                                     constraints_set_mechanics, constraints_set_electricity_magnetism)
    solver.assertFormula(formulas_science)

    # Technology in Society Requirement
    course_variable_tis = solver.mkConst(solver.getStringSort(), "tis_course")

    constraints_tis = [solver.mkTerm(Kind.EQUAL, course_variable_tis,
                                     solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    if constraints_tis:
        constraint_tis = solver.mkTerm(Kind.OR, *constraints_tis)
        # The fix is to avoid creating AND terms with only one child
        formulas_tis = solver.mkTerm(Kind.AND, constraint_tis, solver.mkTrue())
        solver.assertFormula(formulas_tis)

    # Engineering Fundamentals Requirement
    course_variable_cs106b = solver.mkConst(solver.getStringSort(), "cs106b_course")
    course_variable_engr40m_76 = solver.mkConst(solver.getStringSort(), "engr40m_76_course")
    course_variable_intro_making = solver.mkConst(solver.getStringSort(), "intro_making_course")
    course_variable_info_sci_eng = solver.mkConst(solver.getStringSort(), "info_sci_eng_course")

    constraints_cs106b = [solver.mkTerm(Kind.EQUAL, course_variable_cs106b,
                                        solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_engr40m_76 = [solver.mkTerm(Kind.EQUAL, course_variable_engr40m_76,
                                            solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_intro_making = [solver.mkTerm(Kind.EQUAL, course_variable_intro_making,
                                              solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]
    constraints_info_sci_eng = [solver.mkTerm(Kind.EQUAL, course_variable_info_sci_eng,
                                              solver.mkString(course.get("Course_ID"))) for course in transcript.get("Courses_Taken", [])]

    if constraints_cs106b:
        constraint_cs106b = solver.mkTerm(Kind.OR, *constraints_cs106b)
    else:
        constraint_cs106b = solver.mkFalse()

    if constraints_engr40m_76:
        constraint_engr40m_76 = solver.mkTerm(Kind.OR, *constraints_engr40m_76)
    else:
        constraint_engr40m_76 = solver.mkFalse()

    if constraints_intro_making:
        constraint_intro_making = solver.mkTerm(Kind.OR, *constraints_intro_making)
    else:
        constraint_intro_making = solver.mkFalse()

    if constraints_info_sci_eng:
        constraint_info_sci_eng = solver.mkTerm(Kind.OR, *constraints_info_sci_eng)
    else:
        constraint_info_sci_eng = solver.mkFalse()

    constraints_set_engr = [solver.mkTerm(Kind.EQUAL, course_variable_cs106b, solver.mkString('CS106B')),
                            solver.mkTerm(Kind.EQUAL, course_variable_engr40m_76, solver.mkString('ENGR40M')),
                            solver.mkTerm(Kind.EQUAL, course_variable_engr40m_76, solver.mkString('ENGR76')),
                            solver.mkTerm(Kind.EQUAL, course_variable_intro_making, solver.mkString('Intro to Making')),
                            solver.mkTerm(Kind.EQUAL, course_variable_info_sci_eng, solver.mkString('Information Science & Engineering'))]

    formulas_engineering = solver.mkTerm(Kind.AND, constraint_cs106b, constraint_engr40m_76,
                                         constraint_intro_making, constraint_info_sci_eng, *constraints_set_engr)
    solver.assertFormula(formulas_engineering)

    return result_checker(solver, [])

# Test the function with a sample transcript
if __name__ == "__main__":
    transcript_sample = {
        "Courses_Taken": [
            {"Course_ID": "PHYS 41"},
            {"Course_ID": "PHYS 43"},
            {"Course_ID": "CS106B"},
            {"Course_ID": "ENGR40M"},
            {"Course_ID": "ENGR76"},
            {"Course_ID": "Intro to Making"},
            {"Course_ID": "Information Science & Engineering"},
            {"Course_ID": "MATH 19"},
            {"Course_ID": "MATH 20"},
            {"Course_ID": "MATH 21"},
            {"Course_ID": "CS103"}
        ]
    }
    check_transcript(transcript_sample)
