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
    unit_sum = 0
    for course, (taken, units, _) in course_choices.items():
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
            unit_sum += units         
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
            
    solver.assertFormula(
            solver.mkTerm(
                Kind.LEQ,
                solver.mkInteger(unit_sum),
                solver.mkInteger(10),
            )
        )
    result = solver.checkSat()
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat core is: ", core)
        return False

def check_letter_grade(received_grade):

    # Initialize the solver
    solver = cvc5.Solver()

    # Enable proof production (if needed)
    solver.setOption("produce-proofs", "true")

    # Create the string sort
    string_sort = solver.getStringSort()

    # Create a variable representing the input grade
    input_grade = solver.mkConst(string_sort, received_grade)

    # Define the possible letter grades
    grades = ["A+", "A", "A-", "B+", "B", "C+", "C", "C-", "D+", "D", "D-", "F"]

    # Create a term that checks if the input_grade matches any of the letter grades
    is_letter_grade = solver.mkFalse()

    for grade in grades:
        grade_term = solver.mkString(grade)
        is_letter_grade = solver.mkTerm(cvc5.Kind.OR, is_letter_grade, solver.mkTerm(cvc5.Kind.EQUAL, input_grade, grade_term))

    # Assert the constraint
    solver.assertFormula(is_letter_grade)

    # Check satisfiability
    result = solver.checkSat()

    print(f"Result: {result}")

    # If the result is sat, the input is a letter grade
    if result.isSat():
        print("The input is a letter grade.")
        return True
    else:
        print("The input is not a letter grade.")
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
    for course, (taken, unit, grade) in course_choices.items():
        if course in courses:
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, courses[course], solver.mkBoolean(taken)))
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, units[course], solver.mkInteger(unit)))
            check_letter_grade(grade)

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
    solver.setOption("produce-proofs", "true")
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
    for course, (taken, units_earned, grade) in course_choices.items():
        if course in courses:
            # Assert the taken status
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, courses[course], solver.mkBoolean(taken)))
            # Assert the units earned
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, units[course], solver.mkInteger(units_earned)))
            check_letter_grade(grade)

    # Check if the constraints are satisfiable
    result = solver.checkSat()
    print(f"Significant Implementation Requirement Satisfied: {result.isSat()}")
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat core is: ", core)
        return False
 
#helper function    
def create_course_vars_and_constraints(solver, courses, course_choices):
    course_vars = {}
    units = {}
    
    for course in courses:
        if isinstance(course, tuple):
            for sub_course in course:
                if sub_course in course_choices: 
                    course_vars[sub_course+'_attended'] = solver.mkBoolean(course_choices.get(sub_course, [False, 0, "F"])[0])
                    course_vars[sub_course+'_units'] = solver.mkInteger(course_choices.get(sub_course, [False, 0, "F"])[1])
                else:
                    course_vars[sub_course+'_attended'] = solver.mkFalse()
                    course_vars[sub_course+'_units'] = solver.mkInteger(0)
        else:
            if course in course_choices:
                course_vars[course+'_attended'] = solver.mkBoolean(course_choices.get(course, [False, 0, "F"])[0])
                course_vars[course+'_units'] = solver.mkInteger(course_choices.get(course, [False, 0, "F"])[1])
            else:
                    course_vars[course+'_attended'] = solver.mkFalse()
                    course_vars[course+'_units'] = solver.mkInteger(0)
    return course_vars

def check_stanford_master_depth_requirements(course_choices):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setOption("produce-proofs", "true")
    solver.setLogic("ALL")     

    # Definitions of courses in the input format
    courses = [
        'cs221',
        ('cs223a', 'cs224n', 'cs224s', 'cs224u', 'cs224v', 'cs224w', 'cs228', 'cs229', 'cs231a', 'cs231n', 'cs234', 'cs237a', 'cs237b', 'cs238'),
        ('cs205l', 'cs224r', 'cs225a', 'cs227b', 'cs229m', 'cs230', 'cs233', 'cs235', 'cs236', 'cs239', 'cs246', 'cs257', 'cs270', 'cs271', 'cs273a', 'cs273b', 'cs274', 'cs275', 'cs279', 'cs281', 'cs322', 'cs324', 'cs325b', 'cs326', 'cs327a', 'cs329', 'cs330', 'cs331b', 'cs332', 'cs333', 'cs345', 'cs348n', 'cs361', 'cs368', 'cs371', 'cs375', 'cs377', 'cs379', 'cs398', 'cs399', 'cs428a', 'cs428b', 'cs432', 'ee263', 'ee276', 'ee278', 'ee364a', 'ee364b', 'ee377', 'ee378b', 'engr205', 'engr209a', 'msande226', 'msande252', 'psych209', 'stats202', 'stats315a', 'stats315b')
    ]
    
    for course in courses:
        if isinstance(course, tuple):
            for sub_course in course:
                if sub_course in course_choices: 
                    check_letter_grade(course_choices.get(sub_course, [False, 0, "F"])[3])
        else:
            if course in course_choices:
                check_letter_grade(course_choices.get(sub_course, [False, 0, "F"])[3])

    # Definitions of units for each course in the input format
    course_units = [
        'cs221_units',
        'cs223a_units', 'cs224n_units', 'cs224s_units', 'cs224u_units', 'cs224v_units', 'cs224w_units', 'cs228_units', 'cs229_units', 'cs231a_units', 'cs231n_units', 'cs234_units', 'cs237a_units', 'cs237b_units', 'cs238_units',
        'cs205l_units', 'cs224r_units', 'cs225a_units', 'cs227b_units', 'cs229m_units', 'cs230_units', 'cs233_units', 'cs235_units', 'cs236_units', 'cs239_units', 'cs246_units', 'cs257_units', 'cs270_units', 'cs271_units', 'cs273a_units', 'cs273b_units', 'cs274_units', 'cs275_units', 'cs279_units', 'cs281_units', 'cs322_units', 'cs324_units', 'cs325b_units', 'cs326_units', 'cs327a_units', 'cs329_any_suffix_units', 'cs330_units', 'cs331b_units', 'cs332_units', 'cs333_units', 'cs345_units', 'cs348n_units', 'cs361_units', 'cs368_units', 'cs371_units', 'cs375_units', 'cs377_any_suffix_units', 'cs379_any_suffix_units', 'cs398_units', 'cs399_units', 'cs428a_units', 'cs428b_units', 'cs432_units', 'ee263_units', 'ee276_units', 'ee278_units', 'ee364a_units', 'ee364b_units', 'ee377_units', 'ee378b_units', 'engr205_units', 'engr209a_units', 'msande226_units', 'msande252_units', 'psych209_units', 'stats202_units', 'stats315a_units', 'stats315b_units'
    ]

    
    course_vars = create_course_vars_and_constraints(solver, courses, course_choices)

    # Constraints for Artificial Intelligence Depth Requirement
    cs221 = solver.mkTerm(Kind.EQUAL, course_vars['cs221_attended'], solver.mkTrue())
    # Ensuring cs221 is taken
    solver.assertFormula(cs221)
    
    category_b = [
        course_vars['cs223a_attended'],
        course_vars['cs224n_attended'],
        course_vars['cs224s_attended'],
        course_vars['cs224u_attended'],
        course_vars['cs224v_attended'],
        course_vars['cs224w_attended'],
        course_vars['cs228_attended'],
        course_vars['cs229_attended'],
        course_vars['cs231a_attended'],
        course_vars['cs231n_attended'],
        course_vars['cs234_attended'],
        course_vars['cs237a_attended'],
        course_vars['cs237b_attended'],
        course_vars['cs238_attended']
    ]

    category_c = [
        course_vars['cs205l_attended'], course_vars['cs224r_attended'], course_vars['cs225a_attended'], course_vars['cs227b_attended'],
        course_vars['cs229m_attended'], course_vars['cs230_attended'], course_vars['cs233_attended'], course_vars['cs235_attended'],
        course_vars['cs236_attended'], course_vars['cs239_attended'], course_vars['cs246_attended'], course_vars['cs257_attended'],
        course_vars['cs270_attended'], course_vars['cs271_attended'], course_vars['cs273a_attended'], course_vars['cs273b_attended'],
        course_vars['cs274_attended'], course_vars['cs275_attended'], course_vars['cs279_attended'], course_vars['cs281_attended'],
        course_vars['cs322_attended'], course_vars['cs324_attended'], course_vars['cs325b_attended'], course_vars['cs326_attended'],
        course_vars['cs327a_attended'], course_vars['cs329_attended'], course_vars['cs330_attended'],
        course_vars['cs331b_attended'], course_vars['cs332_attended'], course_vars['cs333_attended'], course_vars['cs345_attended'],
        course_vars['cs348n_attended'], course_vars['cs361_attended'], course_vars['cs368_attended'], course_vars['cs371_attended'],
        course_vars['cs375_attended'], course_vars['cs377_attended'], course_vars['cs379_attended'],
        course_vars['cs398_attended'], course_vars['cs399_attended'], course_vars['cs428a_attended'], course_vars['cs428b_attended'],
        course_vars['cs432_attended'], course_vars['ee263_attended'], course_vars['ee276_attended'], course_vars['ee278_attended'],
        course_vars['ee364a_attended'], course_vars['ee364b_attended'], course_vars['ee377_attended'], course_vars['ee378b_attended'],
        course_vars['engr205_attended'], course_vars['engr209a_attended'], course_vars['msande226_attended'], course_vars['msande252_attended'],
        course_vars['psych209_attended'], course_vars['stats202_attended'], course_vars['stats315a_attended'], course_vars['stats315b_attended']
    ]


    # Ensuring at least 4 courses from category (b) are taken
    category_b_attended = [
        course_vars['cs223a_attended'],
        course_vars['cs224n_attended'],
        course_vars['cs224s_attended'],
        course_vars['cs224u_attended'],
        course_vars['cs224v_attended'],
        course_vars['cs224w_attended'],
        course_vars['cs228_attended'],
        course_vars['cs229_attended'],
        course_vars['cs231a_attended'],
        course_vars['cs231n_attended'],
        course_vars['cs234_attended'],
        course_vars['cs237a_attended'],
        course_vars['cs237b_attended'],
        course_vars['cs238_attended']
    ]

    # Convert boolean terms to integer terms (1 if true, 0 if false)
    category_b_attended_int = [solver.mkTerm(Kind.ITE, var, solver.mkInteger(1), solver.mkInteger(0)) for var in category_b_attended]

    # Sum the integer terms
    sum_category_b = solver.mkTerm(Kind.ADD, *category_b_attended_int)

    # Ensure at least 4 courses from category (b) are taken
    solver.assertFormula(solver.mkTerm(Kind.GEQ, sum_category_b, solver.mkInteger(4)))

    # Ensuring at least 21 units from categories (a), (b), and (c)
    unit_vars = [
    course_vars['cs221_units'],
    course_vars['cs223a_units'], course_vars['cs224n_units'], course_vars['cs224s_units'], course_vars['cs224u_units'], course_vars['cs224v_units'],
    course_vars['cs224w_units'], course_vars['cs228_units'], course_vars['cs229_units'], course_vars['cs231a_units'],
    course_vars['cs231n_units'], course_vars['cs234_units'], course_vars['cs237a_units'], course_vars['cs237b_units'],
    course_vars['cs238_units'], course_vars['cs205l_units'], course_vars['cs224r_units'], course_vars['cs225a_units'],
    course_vars['cs227b_units'], course_vars['cs229m_units'], course_vars['cs230_units'], course_vars['cs233_units'],
    course_vars['cs235_units'], course_vars['cs236_units'], course_vars['cs239_units'], course_vars['cs246_units'],
    course_vars['cs257_units'], course_vars['cs270_units'], course_vars['cs271_units'], course_vars['cs273a_units'],
    course_vars['cs273b_units'], course_vars['cs274_units'], course_vars['cs275_units'], course_vars['cs279_units'],
    course_vars['cs281_units'], course_vars['cs322_units'], course_vars['cs324_units'], course_vars['cs325b_units'],
    course_vars['cs326_units'], course_vars['cs327a_units'], course_vars['cs329_units'], course_vars['cs330_units'],
    course_vars['cs331b_units'], course_vars['cs332_units'], course_vars['cs333_units'], course_vars['cs345_units'],
    course_vars['cs348n_units'], course_vars['cs361_units'], course_vars['cs368_units'], course_vars['cs371_units'],
    course_vars['cs375_units'], course_vars['cs377_units'], course_vars['cs379_units'],
    course_vars['cs398_units'], course_vars['cs399_units'], course_vars['cs428a_units'], course_vars['cs428b_units'],
    course_vars['cs432_units'], course_vars['ee263_units'], course_vars['ee276_units'], course_vars['ee278_units'],
    course_vars['ee364a_units'], course_vars['ee364b_units'], course_vars['ee377_units'], course_vars['ee378b_units'],
    course_vars['engr205_units'], course_vars['engr209a_units'], course_vars['msande226_units'], course_vars['msande252_units'],
    course_vars['psych209_units'], course_vars['stats202_units'], course_vars['stats315a_units'], course_vars['stats315b_units']
    ]
    sum_term_all = solver.mkTerm(Kind.ADD, *unit_vars)
    solver.assertFormula(solver.mkTerm(Kind.GEQ, sum_term_all, solver.mkInteger(21)))
    
    # Checking if the solver can meet the constraints
    result = solver.checkSat()
    print(f"Depth Requirement Satisfied: {result.isSat()}")
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat depth requirement core is: ", core)
        proof = solver.getProof()
        print("Proof:")
        print(proof)
        return False


def check_stanford_master_elective_requirements(seminar_choices, other_electives):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setOption("produce-proofs", "true")
    solver.setLogic("ALL")
     # Create a variable for each seminar representing whether it is counted (1) or not (0)
    seminar_vars = create_course_vars_and_constraints(solver, seminar_choices, seminar_choices)
    elective_vars = create_course_vars_and_constraints(solver, other_electives, other_electives)
    
    # Create the formula for the sum of the units of 1-2 unit seminars
    unit_sum = solver.mkInteger(0)
    for seminar, (taken, units, grade) in seminar_choices.items():
        if 1 <= units <= 2:
            # Add a constraint that the variable can only be 0 or 1
            solver.assertFormula(solver.mkTerm(Kind.OR,
                solver.mkTerm(Kind.EQUAL, seminar_vars[seminar+"_units"], solver.mkInteger(0)),
                solver.mkTerm(Kind.EQUAL, seminar_vars[seminar+"_units"], solver.mkInteger(1))
            ))
            # Add the units to the sum
        unit_sum = solver.mkTerm(Kind.ADD, unit_sum, solver.mkTerm(Kind.MULT, seminar_vars[seminar+"_units"], solver.mkInteger(units)))

    # Assert that the sum of the units of 1-2 unit seminars is less than or equal to 3
    solver.assertFormula(solver.mkTerm(Kind.LEQ, unit_sum, solver.mkInteger(3)))

    for elective, (taken, units) in other_electives.items():
        solver.assertFormula(solver.mkTerm(Kind.GEQ, elective_vars[elective+"_units"], solver.mkInteger(3)))
        if "cs129" and "cs229" in other_electives: 
            if elective_vars["cs129_attended"] == True and elective_vars["cs229_attended"] == True: 
                solver.assertFormula(solver.mkTerm(Kind.XOR, elective_vars["cs129_attended"], elective_vars["cs229_attended"]))
        if "cs" in elective:
            solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkInteger(int(elective[2:5])), solver.mkInteger(111)))
            solver.assertFormula(solver.mkTerm(Kind.DISTINCT, solver.mkInteger(int(elective[2:5])), solver.mkInteger(169)))
            solver.assertFormula(solver.mkTerm(Kind.DISTINCT, solver.mkInteger(int(elective[2:5])), solver.mkInteger(198)))
            solver.assertFormula(solver.mkTerm(Kind.DISTINCT, solver.mkInteger(int(elective[2:5])), solver.mkInteger(390)))
        else: #assuming non-cs electives are already approved and technical 
            print(f"There are non-cs elective courses {elective} passing checks: please make sure these courses are approved and technical.\n")
            solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkInteger(int(elective[2:5])), solver.mkInteger(100))) 
        

    # Checking if the solver can meet the constraints
    result = solver.checkSat()
    print(f"Elective Requirement Satisfied: {result.isSat()}")
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat elective requirement core is: ", core)
        return False


def letter_grade_to_points(letter_grade):
    grade_mapping = {
        "A+": 4.3,
        "A": 4.0,
        "A-": 3.7,
        "B+": 3.3,
        "B": 3.0,
        "B-": 2.7,
        "C+": 2.3,
        "C": 2.0,
        "C-": 1.7,
        "D+": 1.3,
        "D": 1.0,
        "D-": 0.7,
        "NP": 0.0,
        "L": 2.0  # Temporary grade
    }

    return grade_mapping.get(letter_grade, "Invalid grade")

def check_stanford_master_additional_requirements(course_choices):
        # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setOption("produce-proofs", "true")
    solver.setLogic("ALL")
    
    graduate_units = 0
    unit_sum = 0
    points = 0 
    for course, (taken, units, grade) in course_choices.items():
        if int(course[2:5]) >= 200: 
            graduate_units += units
        if check_letter_grade(grade):
            earned_points = letter_grade_to_points(grade) * units
            unit_sum += units
            points += earned_points
    
    #at least 36 units must be take for grades
    solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkInteger(unit_sum), solver.mkInteger(36)))
    #check average grade >= B
    solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkReal(points/unit_sum), solver.mkInteger(3)))
     #at least 36 units must be take for grades
    solver.assertFormula(solver.mkTerm(Kind.GEQ, solver.mkInteger(graduate_units), solver.mkInteger(45)))
    
    result = solver.checkSat()
    print(f"Additional Requirement Satisfied: {result.isSat()}")
    if result.isSat():
        return True
    else:
        core = solver.getUnsatCore()
        print("Unsat dditional requirement core is: ", core)
        return False
            
            
