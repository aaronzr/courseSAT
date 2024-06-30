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

    cs154 = solver.mkConst(solver.getBooleanSort(), "CS154")
    cs154_units = solver.mkConst(solver.getIntegerSort(), "CS154_units")

    cs157 = solver.mkConst(solver.getBooleanSort(), "CS157")
    cs157_units = solver.mkConst(solver.getIntegerSort(), "CS157_units")

    cs168 = solver.mkConst(solver.getBooleanSort(), "CS168")
    cs168_units = solver.mkConst(solver.getIntegerSort(), "CS168_units")

    cs254 = solver.mkConst(solver.getBooleanSort(), "CS254")
    cs254_units = solver.mkConst(solver.getIntegerSort(), "CS254_units")

    cs261 = solver.mkConst(solver.getBooleanSort(), "CS261")
    cs261_units = solver.mkConst(solver.getIntegerSort(), "CS261_units")

    cs265 = solver.mkConst(solver.getBooleanSort(), "CS265")
    cs265_units = solver.mkConst(solver.getIntegerSort(), "CS265_units")

    ee364a = solver.mkConst(solver.getBooleanSort(), "EE364A")
    ee364a_units = solver.mkConst(solver.getIntegerSort(), "EE364A_units")

    ee364b = solver.mkConst(solver.getBooleanSort(), "EE364B")
    ee364b_units = solver.mkConst(solver.getIntegerSort(), "EE364B_units")

    phil251 = solver.mkConst(solver.getBooleanSort(), "Phil251")
    phil251_units = solver.mkConst(solver.getIntegerSort(), "Phil251_units")

    cs140 = solver.mkConst(solver.getBooleanSort(), "CS140")
    cs140_units = solver.mkConst(solver.getIntegerSort(), "CS140_units")

    cs140e = solver.mkConst(solver.getBooleanSort(), "CS140E")
    cs140e_units = solver.mkConst(solver.getIntegerSort(), "CS140E_units")

    cs143 = solver.mkConst(solver.getBooleanSort(), "CS143")
    cs143_units = solver.mkConst(solver.getIntegerSort(), "CS143_units")

    cs144 = solver.mkConst(solver.getBooleanSort(), "CS144")
    cs144_units = solver.mkConst(solver.getIntegerSort(), "CS144_units")

    cs149 = solver.mkConst(solver.getBooleanSort(), "CS149")
    cs149_units = solver.mkConst(solver.getIntegerSort(), "CS149_units")

    cs212 = solver.mkConst(solver.getBooleanSort(), "CS212")
    cs212_units = solver.mkConst(solver.getIntegerSort(), "CS212_units")

    cs242 = solver.mkConst(solver.getBooleanSort(), "CS242")
    cs242_units = solver.mkConst(solver.getIntegerSort(), "CS242_units")

    cs243 = solver.mkConst(solver.getBooleanSort(), "CS243")
    cs243_units = solver.mkConst(solver.getIntegerSort(), "CS243_units")

    cs244 = solver.mkConst(solver.getBooleanSort(), "CS244")
    cs244_units = solver.mkConst(solver.getIntegerSort(), "CS244_units")

    cs244b = solver.mkConst(solver.getBooleanSort(), "CS244B")
    cs244b_units = solver.mkConst(solver.getIntegerSort(), "CS244B_units")

    cs295 = solver.mkConst(solver.getBooleanSort(), "CS295")
    cs295_units = solver.mkConst(solver.getIntegerSort(), "CS295_units")

    cs316 = solver.mkConst(solver.getBooleanSort(), "CS316")
    cs316_units = solver.mkConst(solver.getIntegerSort(), "CS316_units")

    cs358 = solver.mkConst(solver.getBooleanSort(), "CS358")
    cs358_units = solver.mkConst(solver.getIntegerSort(), "CS358_units")

    ee180 = solver.mkConst(solver.getBooleanSort(), "EE180")
    ee180_units = solver.mkConst(solver.getIntegerSort(), "EE180_units")

    ee282 = solver.mkConst(solver.getBooleanSort(), "EE282")
    ee282_units = solver.mkConst(solver.getIntegerSort(), "EE282_units")

    ee382e = solver.mkConst(solver.getBooleanSort(), "EE382E")
    ee382e_units = solver.mkConst(solver.getIntegerSort(), "EE382E_units")

    cs145 = solver.mkConst(solver.getBooleanSort(), "CS145")
    cs145_units = solver.mkConst(solver.getIntegerSort(), "CS145_units")

    cs147 = solver.mkConst(solver.getBooleanSort(), "CS147")
    cs147_units = solver.mkConst(solver.getIntegerSort(), "CS147_units")

    cs148 = solver.mkConst(solver.getBooleanSort(), "CS148")
    cs148_units = solver.mkConst(solver.getIntegerSort(), "CS148_units")

    cs155 = solver.mkConst(solver.getBooleanSort(), "CS155")
    cs155_units = solver.mkConst(solver.getIntegerSort(), "CS155_units")

    cs173 = solver.mkConst(solver.getBooleanSort(), "CS173")
    cs173_units = solver.mkConst(solver.getIntegerSort(), "CS173_units")

    cs221 = solver.mkConst(solver.getBooleanSort(), "CS221")
    cs221_units = solver.mkConst(solver.getIntegerSort(), "CS221_units")

    cs223a = solver.mkConst(solver.getBooleanSort(), "CS223A")
    cs223a_units = solver.mkConst(solver.getIntegerSort(), "CS223A_units")

    cs224n = solver.mkConst(solver.getBooleanSort(), "CS224N")
    cs224n_units = solver.mkConst(solver.getIntegerSort(), "CS224N_units")

    cs224u = solver.mkConst(solver.getBooleanSort(), "CS224U")
    cs224u_units = solver.mkConst(solver.getIntegerSort(), "CS224U_units")

    cs224w = solver.mkConst(solver.getBooleanSort(), "CS224W")
    cs224w_units = solver.mkConst(solver.getIntegerSort(), "CS224W_units")

    cs227b = solver.mkConst(solver.getBooleanSort(), "CS227B")
    cs227b_units = solver.mkConst(solver.getIntegerSort(), "CS227B_units")

    cs228 = solver.mkConst(solver.getBooleanSort(), "CS228")
    cs228_units = solver.mkConst(solver.getIntegerSort(), "CS228_units")

    cs229 = solver.mkConst(solver.getBooleanSort(), "CS229")
    cs229_units = solver.mkConst(solver.getIntegerSort(), "CS229_units")

    cs229m = solver.mkConst(solver.getBooleanSort(), "CS229M")
    cs229m_units = solver.mkConst(solver.getIntegerSort(), "CS229M_units")

    cs231a = solver.mkConst(solver.getBooleanSort(), "CS231A")
    cs231a_units = solver.mkConst(solver.getIntegerSort(), "CS231A_units")

    cs231n = solver.mkConst(solver.getBooleanSort(), "CS231N")
    cs231n_units = solver.mkConst(solver.getIntegerSort(), "CS231N_units")

    cs234 = solver.mkConst(solver.getBooleanSort(), "CS234")
    cs234_units = solver.mkConst(solver.getIntegerSort(), "CS234_units")

    cs236 = solver.mkConst(solver.getBooleanSort(), "CS236")
    cs236_units = solver.mkConst(solver.getIntegerSort(), "CS236_units")

    cs237a = solver.mkConst(solver.getBooleanSort(), "CS237A")
    cs237a_units = solver.mkConst(solver.getIntegerSort(), "CS237A_units")

    cs245 = solver.mkConst(solver.getBooleanSort(), "CS245")
    cs245_units = solver.mkConst(solver.getIntegerSort(), "CS245_units")

    cs246 = solver.mkConst(solver.getBooleanSort(), "CS246")
    cs246_units = solver.mkConst(solver.getIntegerSort(), "CS246_units")

    cs247 = solver.mkConst(solver.getBooleanSort(), "CS247")
    cs247_units = solver.mkConst(solver.getIntegerSort(), "CS247_units")

    cs248 = solver.mkConst(solver.getBooleanSort(), "CS248")
    cs248_units = solver.mkConst(solver.getIntegerSort(), "CS248_units")

    cs248a = solver.mkConst(solver.getBooleanSort(), "CS248A")
    cs248a_units = solver.mkConst(solver.getIntegerSort(), "CS248A_units")

    cs251 = solver.mkConst(solver.getBooleanSort(), "CS251")
    cs251_units = solver.mkConst(solver.getIntegerSort(), "CS251_units")

    cs255 = solver.mkConst(solver.getBooleanSort(), "CS255")
    cs255_units = solver.mkConst(solver.getIntegerSort(), "CS255_units")

    cs273a = solver.mkConst(solver.getBooleanSort(), "CS273A")
    cs273a_units = solver.mkConst(solver.getIntegerSort(), "CS273A_units")

    cs273b = solver.mkConst(solver.getBooleanSort(), "CS273B")
    cs273b_units = solver.mkConst(solver.getIntegerSort(), "CS273B_units")

    cs279 = solver.mkConst(solver.getBooleanSort(), "CS279")
    cs279_units = solver.mkConst(solver.getIntegerSort(), "CS279_units")

    cs345 = solver.mkConst(solver.getBooleanSort(), "CS345")
    cs345_units = solver.mkConst(solver.getIntegerSort(), "CS345_units")

    cs347 = solver.mkConst(solver.getBooleanSort(), "CS347")
    cs347_units = solver.mkConst(solver.getIntegerSort(), "CS347_units")

    cs348a = solver.mkConst(solver.getBooleanSort(), "CS348A")
    cs348a_units = solver.mkConst(solver.getIntegerSort(), "CS348A_units")

    cs348b = solver.mkConst(solver.getBooleanSort(), "CS348B")
    cs348b_units = solver.mkConst(solver.getIntegerSort(), "CS348B_units")

    cs348c = solver.mkConst(solver.getBooleanSort(), "CS348C")
    cs348c_units = solver.mkConst(solver.getIntegerSort(), "CS348C_units")

    cs348e = solver.mkConst(solver.getBooleanSort(), "CS348E")
    cs348e_units = solver.mkConst(solver.getIntegerSort(), "CS348E_units")

    cs348i = solver.mkConst(solver.getBooleanSort(), "CS348I")
    cs348i_units = solver.mkConst(solver.getIntegerSort(), "CS348I_units")

    cs348k = solver.mkConst(solver.getBooleanSort(), "CS348K")
    cs348k_units = solver.mkConst(solver.getIntegerSort(), "CS348K_units")

    cs355 = solver.mkConst(solver.getBooleanSort(), "CS355")
    cs355_units = solver.mkConst(solver.getIntegerSort(), "CS355_units")

    cs356 = solver.mkConst(solver.getBooleanSort(), "CS356")
    cs356_units = solver.mkConst(solver.getIntegerSort(), "CS356_units")

    cs373 = solver.mkConst(solver.getBooleanSort(), "CS373")
    cs373_units = solver.mkConst(solver.getIntegerSort(), "CS373_units")

    cs152 = solver.mkConst(solver.getBooleanSort(), "CS152")
    cs152_units = solver.mkConst(solver.getIntegerSort(), "CS152_units")

    cs181 = solver.mkConst(solver.getBooleanSort(), "CS181")
    cs181_units = solver.mkConst(solver.getIntegerSort(), "CS181_units")

    cs182 = solver.mkConst(solver.getBooleanSort(), "CS182")
    cs182_units = solver.mkConst(solver.getIntegerSort(), "CS182_units")

    cs256 = solver.mkConst(solver.getBooleanSort(), "CS256")
    cs256_units = solver.mkConst(solver.getIntegerSort(), "CS256_units")

    cs281 = solver.mkConst(solver.getBooleanSort(), "CS281")
    cs281_units = solver.mkConst(solver.getIntegerSort(), "CS281_units")

    cs329t = solver.mkConst(solver.getBooleanSort(), "CS329T")
    cs329t_units = solver.mkConst(solver.getIntegerSort(), "CS329T_units")

    cs384 = solver.mkConst(solver.getBooleanSort(), "CS384")
    cs384_units = solver.mkConst(solver.getIntegerSort(), "CS384_units")

    amstud133 = solver.mkConst(solver.getBooleanSort(), "AMSTUD133")
    amstud133_units = solver.mkConst(solver.getIntegerSort(), "AMSTUD133_units")

    amstud145 = solver.mkConst(solver.getBooleanSort(), "AMSTUD145")
    amstud145_units = solver.mkConst(solver.getIntegerSort(), "AMSTUD145_units")

    anthro132d = solver.mkConst(solver.getBooleanSort(), "ANTHRO132D")
    anthro132d_units = solver.mkConst(solver.getIntegerSort(), "ANTHRO132D_units")

    comm118s = solver.mkConst(solver.getBooleanSort(), "COMM118S")
    comm118s_units = solver.mkConst(solver.getIntegerSort(), "COMM118S_units")

    comm120w = solver.mkConst(solver.getBooleanSort(), "COMM120W")
    comm120w_units = solver.mkConst(solver.getIntegerSort(), "COMM120W_units")

    comm124 = solver.mkConst(solver.getBooleanSort(), "COMM124")
    comm124_units = solver.mkConst(solver.getIntegerSort(), "COMM124_units")

    comm130d = solver.mkConst(solver.getBooleanSort(), "COMM130D")
    comm130d_units = solver.mkConst(solver.getIntegerSort(), "COMM130D_units")

    comm145 = solver.mkConst(solver.getBooleanSort(), "COMM145")
    comm145_units = solver.mkConst(solver.getIntegerSort(), "COMM145_units")

    comm154 = solver.mkConst(solver.getBooleanSort(), "COMM154")
    comm154_units = solver.mkConst(solver.getIntegerSort(), "COMM154_units")

    comm166 = solver.mkConst(solver.getBooleanSort(), "COMM166")
    comm166_units = solver.mkConst(solver.getIntegerSort(), "COMM166_units")

    comm186w = solver.mkConst(solver.getBooleanSort(), "COMM186W")
    comm186w_units = solver.mkConst(solver.getIntegerSort(), "COMM186W_units")

    comm230a = solver.mkConst(solver.getBooleanSort(), "COMM230A")
    comm230a_units = solver.mkConst(solver.getIntegerSort(), "COMM230A_units")

    comm230b = solver.mkConst(solver.getBooleanSort(), "COMM230B")
    comm230b_units = solver.mkConst(solver.getIntegerSort(), "COMM230B_units")

    comm230c = solver.mkConst(solver.getBooleanSort(), "COMM230C")
    comm230c_units = solver.mkConst(solver.getIntegerSort(), "COMM230C_units")

    desinst215 = solver.mkConst(solver.getBooleanSort(), "DESINST215")
    desinst215_units = solver.mkConst(solver.getIntegerSort(), "DESINST215_units")

    desinst240 = solver.mkConst(solver.getBooleanSort(), "DESINST240")
    desinst240_units = solver.mkConst(solver.getIntegerSort(), "DESINST240_units")

    earthsys213 = solver.mkConst(solver.getBooleanSort(), "EARTHSYS213")
    earthsys213_units = solver.mkConst(solver.getIntegerSort(), "EARTHSYS213_units")

    english184d = solver.mkConst(solver.getBooleanSort(), "ENGLISH184D")
    english184d_units = solver.mkConst(solver.getIntegerSort(), "ENGLISH184D_units")

    engr248 = solver.mkConst(solver.getBooleanSort(), "ENGR248")
    engr248_units = solver.mkConst(solver.getIntegerSort(), "ENGR248_units")

    history244f = solver.mkConst(solver.getBooleanSort(), "HISTORY244F")
    history244f_units = solver.mkConst(solver.getIntegerSort(), "HISTORY244F_units")

    intlpol268 = solver.mkConst(solver.getBooleanSort(), "INTLPOL268")
    intlpol268_units = solver.mkConst(solver.getIntegerSort(), "INTLPOL268_units")

    law4039 = solver.mkConst(solver.getBooleanSort(), "LAW4039")
    law4039_units = solver.mkConst(solver.getIntegerSort(), "LAW4039_units")

    me177 = solver.mkConst(solver.getBooleanSort(), "ME177")
    me177_units = solver.mkConst(solver.getIntegerSort(), "ME177_units")

    mse193 = solver.mkConst(solver.getBooleanSort(), "MS&E193")
    mse193_units = solver.mkConst(solver.getIntegerSort(), "MS&E193_units")

    mse231 = solver.mkConst(solver.getBooleanSort(), "MS&E231")
    mse231_units = solver.mkConst(solver.getIntegerSort(), "MS&E231_units")

    mse234 = solver.mkConst(solver.getBooleanSort(), "MS&E234")
    mse234_units = solver.mkConst(solver.getIntegerSort(), "MS&E234_units")

    mse254 = solver.mkConst(solver.getBooleanSort(), "MS&E254")
    mse254_units = solver.mkConst(solver.getIntegerSort(), "MS&E254_units")

    polisci150a = solver.mkConst(solver.getBooleanSort(), "POLISCI150A")
    polisci150a_units = solver.mkConst(solver.getIntegerSort(), "POLISCI150A_units")

    psych215 = solver.mkConst(solver.getBooleanSort(), "PSYCH215")
    psych215_units = solver.mkConst(solver.getIntegerSort(), "PSYCH215_units")

    publpol103f = solver.mkConst(solver.getBooleanSort(), "PUBLPOL103F")
    publpol103f_units = solver.mkConst(solver.getIntegerSort(), "PUBLPOL103F_units")

    publpol353b = solver.mkConst(solver.getBooleanSort(), "PUBLPOL353B")
    publpol353b_units = solver.mkConst(solver.getIntegerSort(), "PUBLPOL353B_units")
    
    #manully fixed the list from LLM raw output by changing them from string to variable and
    #converting all uper case to lower case
    course_requirements = [
        (cs154, cs157, cs168,  cs254, cs261, cs265, ee364a, ee364b,  phil251),
        (cs140, cs140e, cs143, cs144, cs149, cs212, cs242, cs243, cs244, cs244b,  cs295, cs316, cs358, ee180, ee282, ee382e),
        (cs145, cs147, cs148, cs155, cs173, cs221, cs223a, cs224n, cs224u, cs224w, cs227b, cs228, cs229, cs229m, cs231a, cs231n, cs234, cs236, cs237a, cs245, cs246, cs247, cs248, cs248a, cs251,  cs255, cs273a, cs273b, cs279, cs345, cs347, cs348a, cs348b, cs348c, cs348e, cs348i, cs348k, cs355, cs356, cs373),
        (cs152, cs181,  cs182, cs256, cs281, cs329t, cs384, amstud133, amstud145, anthro132d, comm118s, comm120w, comm124, comm130d, comm145, comm154, comm166, comm186w, comm230a, comm230b, comm230c, desinst215, desinst240, earthsys213, english184d, engr248, history244f, intlpol268, law4039, me177,  mse193,  mse231,  mse234, mse254, polisci150a, psych215, publpol103f, publpol353b)
        ]
    
    #Since the solver checking code is formulaic (same as the function above),
    #the code below are copy-pasted from the function above. 
    for requirement in course_requirements:
        if isinstance(requirement, tuple):
            solver.assertFormula(solver.mkTerm(Kind.OR, *requirement))
        else:
            solver.assertFormula(
                solver.mkTerm(Kind.EQUAL, requirement, solver.mkTrue())
            )

    #manually constructed 
    course_units = [
        #fix with items 
        cs154_units, cs157_units, cs168_units,  cs254_units, cs261_units, cs265_units, ee364a_units, ee364b_units,  phil251_units,\
        cs140_units, cs140e_units, cs143_units, cs144_units, cs149_units, cs212_units, cs242_units, cs243_units, cs244_units, cs244b_units,  cs295_units, cs316_units, cs358_units, ee180_units, ee282_units, ee382e_units,\
        cs145_units, cs147_units, cs148_units, cs155_units, cs173_units, cs221_units, cs223a_units, cs224n_units, cs224u_units, cs224w_units, cs227b_units, cs228_units, cs229_units, cs229m_units, cs231a_units, cs231n_units, cs234_units, cs236_units, cs237a_units, cs245_units, cs246_units, cs247_units, cs248_units, cs248a_units, cs251_units,  cs255_units, cs273a_units, cs273b_units, cs279_units, cs345_units, cs347_units, cs348a_units, cs348b_units, cs348c_units, cs348e_units, cs348i_units, cs348k_units, cs355_units, cs356_units, cs373_units,\
        cs152_units, cs181_units,  cs182_units, cs256_units, cs281_units, cs329t_units, cs384_units, amstud133_units, amstud145_units, anthro132d_units, comm118s_units, comm120w_units, comm124_units, comm130d_units, comm145_units, comm154_units, comm166_units, comm186w_units, comm230a_units, comm230b_units, comm230c_units, desinst215_units, desinst240_units, earthsys213_units, english184d_units, engr248_units, history244f_units, intlpol268_units, law4039_units, me177_units,  mse193_units,  mse231_units,  mse234_units, mse254_units, polisci150a_units, psych215_units, publpol103f_units, publpol353b_units]
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


