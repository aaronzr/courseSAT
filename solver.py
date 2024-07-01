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
                    solver.mkInteger(0),
                )
            )

    result = solver.checkSat()
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat core is: ", core)
        return False

def check_stanford_master_breadth_requirements(course_choices):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")

    # Defining courses and their respective units
    course_list = [
        # Area A: Mathematical and Theoretical Foundations
        ('cs154', 'cs157', 'cs168', 'cs254', 'cs261', 'cs265', 'ee364a', 'ee364b', 'phil251'),
        # Area B: Computer Systems
        ('cs140', 'cs140e', 'cs143', 'cs144', 'cs149', 'cs212', 'cs242', 'cs243', 'cs244', 'cs244b', 'cs295', 'cs316', 'cs358', 'ee180', 'ee282', 'ee382e'),
        # Area C: Applications
        ('cs145', 'cs147', 'cs148', 'cs155', 'cs173', 'cs221', 'cs223a', 'cs224n', 'cs224u', 'cs224w', 'cs227b', 'cs228', 'cs229', 'cs229m', 'cs231a', 'cs231n', 'cs234', 'cs236', 'cs237a', 'cs245', 'cs246', 'cs247', 'cs248', 'cs248a', 'cs251', 'cs255', 'cs273a', 'cs273b', 'cs279', 'cs345', 'cs347', 'cs348a', 'cs348b', 'cs348c', 'cs348e', 'cs348i', 'cs348k', 'cs355', 'cs356', 'cs373'),
        # Area D: Computing and Society
        ('cs152', 'cs181', 'cs182', 'cs256', 'cs281', 'cs329t', 'cs384', 'amstud133', 'amstud145', 'anthro132d', 'comm118s', 'comm120w', 'comm124', 'comm130d', 'comm145', 'comm154', 'comm166', 'comm186w', 'comm230a', 'comm230b', 'comm230c', 'desinst215', 'desinst240', 'earthsys213', 'english184d', 'engr248', 'history244f', 'intlpol268', 'law4039', 'me177', 'msande193', 'msande231', 'msande234', 'msande254', 'polisci150a', 'psych215', 'publpol103f', 'publpol353b')
    ]

    # Create terms for each course
    courses = {course: solver.mkConst(solver.getBooleanSort(), str(course)) for area in course_list for course in area}

    # Create terms for each course's units
    units = {course: solver.mkConst(solver.getIntegerSort(),f"{course}_units") for area in course_list for course in area}

    # Assert user input choices
    for course, (taken, unit) in course_choices.items():
        if course in courses:
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, courses[course], solver.mkBoolean(taken)))
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, units[course], solver.mkInteger(unit)))

    # Breadth Requirement Constraints
    # At least 3 courses, each from a different area
    for area in course_list:
        terms = [
            solver.mkTerm(Kind.AND, courses[course], solver.mkTerm(Kind.GEQ, units[course], solver.mkInteger(3)))
            for course in area
        ]
        
        if len(terms) > 1:
            solver.assertFormula(solver.mkTerm(Kind.OR, *terms))
        elif len(terms) == 1:
            solver.assertFormula(terms[0])

    # Ensure at least 3 different areas have at least one course
    area_selections = [
        solver.mkTerm(
            Kind.OR,
            *[
                solver.mkTerm(Kind.AND, courses[course], solver.mkTerm(Kind.GEQ, units[course], solver.mkInteger(3)))
                for course in area
            ]
        )
        for area in course_list
    ]

    # Convert boolean selections to integer (1 for true, 0 for false)
    area_integers = [
        solver.mkTerm(Kind.ITE, selection, solver.mkInteger(1), solver.mkInteger(0))
        for selection in area_selections
    ]

    solver.assertFormula(
        solver.mkTerm(
            Kind.GEQ,
            solver.mkTerm(
                Kind.ADD,
                *area_integers
            ),
            solver.mkInteger(3)
        )
    )
    # Ensure each of the selected courses has at least 3 units and is taken for a grade (True)
    for course in course_choices:
        if course in courses:
            solver.assertFormula(solver.mkTerm(Kind.GEQ, units[course], solver.mkInteger(3)))
            solver.assertFormula(courses[course])

    # Checking if the solver can meet the constraints
    result = solver.checkSat()
    print(f"Breadth Requirement Satisfied: {result.isSat()}")
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat core is: ", core)
        return False

def check_stanford_master_implementation_requirements(course_choices):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")

    significant_courses = [
    'cs140', 'cs140e', 'cs143', 'cs144', 'cs145', 'cs148', 'cs151', 'cs190', 
    'cs210b', 'cs212', 'cs221', 'cs227b', 'cs231n', 'cs243', ('cs248', 'cs248a'), 'cs341'
    ]

    # Create terms for each course
    courses = {}
    units = {}
    for item in significant_courses:
        if isinstance(item, str):
            courses[item] = solver.mkConst(solver.getBooleanSort(), item)
            units[item] = solver.mkConst(solver.getIntegerSort(), item + "_units")
        elif isinstance(item, tuple):
            for course in item:
                courses[course] = solver.mkConst(solver.getBooleanSort(), course)
                units[course] = solver.mkConst(solver.getIntegerSort(), course + "_units")

    # Create a constraint to make sure at least one significant course is taken and has at least 1 unit
    at_least_one_significant_course = solver.mkTerm(
        Kind.OR, *[
            solver.mkTerm(Kind.AND, courses[course], solver.mkTerm(Kind.GEQ, units[course], solver.mkInteger(1)))
            for course in courses
        ]
    )

    # Add the constraint to the solver
    solver.assertFormula(at_least_one_significant_course)

    # Assert the course choices
    for course, (taken, units_earned) in course_choices.items():
        if course in courses:
            # Assert the taken status
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, courses[course], solver.mkBoolean(taken)))
            # Assert the units earned
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, units[course], solver.mkInteger(units_earned)))

    # Check if the constraints are satisfiable
    result = solver.checkSat()
    print(f"Significant Implementation Requirement Satisfied: {result.isSat()}")
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat core is: ", core)
        return False
        
def check_stanford_master_depth_requirements(course_choices):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setLogic("ALL")     