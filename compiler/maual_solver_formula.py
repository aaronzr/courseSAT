import cvc5
from cvc5 import Solver, Kind

#Based on the natural langauge sentences test input: 

test_input = {
	"cs103": [True, 3, "A"],
	"cs161": [True, 4, "B+"],              
    }

def formula(test_input): 
	solver = cvc5.Solver()
	solver.setOption("produce-unsat-cores", "true")
	solver.setOption("produce-models", "true")
	solver.setLogic("ALL")
	#set up background
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

	unit_sum = 0
	for course, (taken, units, _) in test_input.items():
		if taken:
			solver.assertFormula(
			solver.mkTerm(Kind.EQUAL, locals()[course.lower()], solver.mkTrue())
			)
			solver.assertFormula(
			solver.mkTerm(
			Kind.EQUAL,
			locals()[f"{course.lower()}_units"],
			solver.mkInteger(units),))
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
	#check  constraint: The total number of units must be greater than or equal to 45
	formula = solver.mkTerm(Kind.GEQ, solver.mkInteger(unit_sum), solver.mkInteger(45))
	solver.assertFormula(formula)
	#
	# Course requirements
	# At least one course from each group must be true
	course_requirements = [
	cs103,
	cs161,
	(cs107, cs107e),
	(cs110, cs111),
	(cs109, ee178, stat116, cme106, msande220),
	]
	#check constraint: students need to satisfy each sub requirement of foundations requirements
	for requirement in course_requirements:
		if isinstance(requirement, tuple):
			solver.assertFormula(solver.mkTerm(Kind.OR, *requirement))
		else:
			solver.assertFormula(solver.mkTerm(Kind.EQUAL, requirement, solver.mkTrue()))

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
			solver.mkInteger(3),))
	    
	result = solver.checkSat()
	if result.isSat():
		return True
	else:
		core = solver.getUnsatCore()
		print("Unsat core is: ", core)
		return False

formula(test_input)