import cvc5
from cvc5 import Kind


def check_stanford_master_foundamental_requirements(course_choices):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")

    # Define course variables

    # Logic courses
    cs103 = solver.mkConst(solver.getBooleanSort(), "CS103")
    cs103_units = solver.mkConst(solver.getIntegerSort(), "CS103_units")

    # Algorithmic Analysis courses
    cs161 = solver.mkConst(solver.getBooleanSort(), "CS161")
    cs161_units = solver.mkConst(solver.getIntegerSort(), "CS161_units")

    # Computer Organization courses
    cs107 = solver.mkConst(solver.getBooleanSort(), "CS107")
    cs107e = solver.mkConst(solver.getBooleanSort(), "CS107E")

    cs107_units = solver.mkConst(solver.getIntegerSort(), "CS107_units")
    cs107e_units = solver.mkConst(solver.getIntegerSort(), "CS107E_units")

    # Principles of Computer Systems courses
    cs110 = solver.mkConst(solver.getBooleanSort(), "CS110")
    cs111 = solver.mkConst(solver.getBooleanSort(), "CS111")

    cs110_units = solver.mkConst(solver.getIntegerSort(), "CS110_units")
    cs111_units = solver.mkConst(solver.getIntegerSort(), "CS111_units")

    # Probability courses
    cs109 = solver.mkConst(solver.getBooleanSort(), "CS109")
    ee178 = solver.mkConst(solver.getBooleanSort(), "EE178")
    stat116 = solver.mkConst(solver.getBooleanSort(), "Stat116")
    cme106 = solver.mkConst(solver.getBooleanSort(), "CME106")
    msande220 = solver.mkConst(solver.getBooleanSort(), "MSandE220")

    cs109_units = solver.mkConst(solver.getIntegerSort(), "CS109_units")
    ee178_units = solver.mkConst(solver.getIntegerSort(), "EE178_units")
    stat116_units = solver.mkConst(solver.getIntegerSort(), "Stat116_units")
    cme106_units = solver.mkConst(solver.getIntegerSort(), "CME106_units")
    msande220_units = solver.mkConst(solver.getIntegerSort(), "MSandE220_units")

    # Course requirements
    # At least one course from each group must be true
    course_requirements = [
        cs103,
        cs161,
        (cs107, cs107e),
        (cs110, cs111),
        (cs109, ee178, stat116, cme106, msande220),
    ]
    for requirement in course_requirements:
        if isinstance(requirement, tuple):
            solver.assertFormula(solver.mkTerm(Kind.OR, *requirement))
        else:
            solver.assertFormula(
                solver.mkTerm(Kind.EQUAL, requirement, solver.mkTrue())
            )

    # all the units must be greater than or equal to 3
    course_units = [
        cs103_units,
        cs161_units,
        cs107_units,
        cs107e_units,
        cs110_units,
        cs111_units,
        cs109_units,
        ee178_units,
        stat116_units,
        cme106_units,
        msande220_units,
    ]
    for unit in course_units:
        solver.assertFormula(
            solver.mkTerm(
                Kind.GEQ,
                unit,
                solver.mkInteger(3),
            )
        )

    # Check satisfiability
    result = solver.checkSat()
    if result.isSat():
        print("The model is satisfiable.")
    else:
        print("The model is unsatisfiable.")

    solver.push()
    # Add the course choices
    for course, (taken, units) in course_choices.items():
        if taken:
            solver.assertFormula(
                solver.mkTerm(Kind.EQUAL, locals()[course.lower()], solver.mkTrue())
            )
            solver.assertFormula(
                solver.mkTerm(
                    Kind.EQUAL,
                    locals()[f"{course.lower()}_units"],
                    solver.mkInteger(units),
                )
            )
        else:
            solver.assertFormula(
                solver.mkTerm(Kind.EQUAL, locals()[course.lower()], solver.mkFalse())
            )
            solver.assertFormula(
                solver.mkTerm(
                    Kind.EQUAL,
                    locals()[f"{course.lower()}_units"],
                    solver.mkInteger(3),
                )
            )

    result = solver.checkSat()
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat core is: ", core)
        return False


# Couse choices along with untis taken

def test_foundamental_requrements():
    course_choices = {
        "cs109": [False, 0],
        "ee178": [False, 0],
        "stat116": [False, 4],
        "cme106": [False, 0],
        "cs103": [True, 4],
        "cs161": [True, 4],
        "cs107": [True, 4],
        "cs107e": [False, 0],
        "cs110": [False, 0],
        "cs111": [True, 3],
        "msande220": [False, 0],
    }

    sat_course_choices = {
        "cs109": [True, 0],
        "ee178": [True, 3],
        "stat116": [True, 3],
        "cme106": [True, 3],
        "cs103": [True, 3],
        "cs161": [True, 3],
        "cs107": [True, 3],
        "cs107e": [True, 3],
        "cs110": [True, 3],
        "cs111": [True, 3],
        "msande220": [True, 4],
    }
    print(check_stanford_master_foundamental_requirements(course_choices))
    print(check_stanford_master_foundamental_requirements(sat_course_choices))

if __name__ == "__main__":
    test_foundamental_requrements()
