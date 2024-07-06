import os
import sys
import cvc5
import json
#from process import *
from cvc5 import Kind
from pysmt.typing import *
from pysmt.shortcuts import *
from pysmt.shortcuts import Symbol, And, Or, EqualsOrIff, String, get_model


schema_path = "../schema_results/stanford_transcript1.json"
with open(schema_path, 'r') as file:
	transcript = json.load(file)
#NL:total earned units must be greater than or equal to 45
    # Initialize solver

'''
EXAMPLE 1: 
Pick one of the courses: (100, 101, 102):  ______ (course1)
Pick one of the courses: (101, 102, 103):  ______ (course2)
The same course cannot be used to satisfy two different requirements.


Course1 is \in transcript[*].course; 
Course2 is \in transcript[*].course;
Course1 is in one of (100,101,102)
Course2 is in one of (101, 102, 103)
Course1 <> course2
'''

def result_checker(solver):
	result = solver.checkSat()

	# Print the result
	print("Satisfiability:", result)

	# Get and print the model if the formula is satisfiable
	if result.isSat():
		print("SAT")
		'''
		model = solver.getValue(course_variable_1)
		print("Model for course_variable_1:", model)
		model = solver.getValue(course_variable_2)
		print("Model for course_variable_2:", model)
		'''
	else: 
		core = solver.getUnsatCore()
		print("Unsat dditional requirement core is: ", core)

def solver_init(): 
	solver = cvc5.Solver()
	solver.setOption("produce-unsat-cores", "true")
	solver.setOption("produce-models", "true")
	solver.setLogic("ALL")
	return solver 
 
def cvc5_example_1():
	solver = cvc5.Solver()
	solver.setOption("produce-unsat-cores", "true")
	solver.setOption("produce-models", "true")
	solver.setLogic("ALL")
 

	# Create varaibles for each intended course variables: mkConst is not making 
	#the variable  constant 
	course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
	course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")
	#Course1 is \in transcript[*].course; 
	#Course2 is \in transcript[*].course;
	constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course.get("Course_ID")))for course in transcript.get("Courses_Taken", [])]
	constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course.get("Course_ID")))for course in transcript.get("Courses_Taken", [])]
	constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)
	constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)
 	#Course1 is in one of (100,101,102)
	#Course2 is in one of (101, 102, 103)
	constraints_set3 = [solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString(course_unit))for course_unit in ['CS 100', 'CS 101', 'CS 102']]
	constraints_set4 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course_unit))for course_unit in ['CS 101', 'CS 102', 'CS 103']]
	constraint_3 = solver.mkTerm(Kind.OR, *constraints_set3)
	constraint_4 = solver.mkTerm(Kind.OR, *constraints_set4)
	#AND all previous individual constraints
	#Course1 is \in transcript[*].course AND 
	#Course2 is \in transcript[*].course AND
  	#Course1 is in one of (100,101,102)AND
	#Course2 is in one of (101, 102, 103)AND
 
	constraint_5 = solver.mkTerm(Kind.AND, constraint_1, constraint_2, constraint_3, constraint_4)
	#The same course cannot be used to satisfy two different requirements: 
	#course_1 == coures_2
	constraint_6 = solver.mkTerm(Kind.EQUAL, course_variable_1, course_variable_2)
	#NEGATE(course_1 == coures_2)=> course_1 != coures_2
	constraint_7 = solver.mkTerm(Kind.NOT, constraint_6)
	#final formula:
	formula = solver.mkTerm(Kind.AND, constraint_7, constraint_5)
	print(formula)
	solver.assertFormula(formula)
	result = solver.checkSat()

	# Print the result
	print("Satisfiability:", result)

	# Get and print the model if the formula is satisfiable
	if result.isSat():
		model = solver.getValue(course_variable_1)
		print("Model for course_variable_1:", model)
		model = solver.getValue(course_variable_2)
		print("Model for course_variable_2:", model)
	else: 
		core = solver.getUnsatCore()
		print("Unsat dditional requirement core is: ", core)


'''
EXAMPLE 2: 
Satisfy the requirements listed in each of the following areas:
   - Logic, Automata & Complexity (CS103)
   - Probability (CS109, Stat116, CME106, MS&E220, or EE178)
   - Algorithmic Analysis (CS161)
   - Computer Organ & Sys (CS107 or 107E)
   - Principles of Computer Systems (CS110 or CS111)
'''
def cvc5_example_2():
	solver = solver_init()
	course_variable_1 = solver.mkConst(solver.getStringSort(), "course1")
	course_variable_2 = solver.mkConst(solver.getStringSort(), "course2")
	course_variable_3 = solver.mkConst(solver.getStringSort(), "course3")
	course_variable_4 = solver.mkConst(solver.getStringSort(), "course4")
	course_variable_5 = solver.mkConst(solver.getStringSort(), "course5")

	constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable_1, \
	 solver.mkString(course.get("Course_ID").strip()))for course in transcript.get("Courses_Taken", [])]
	constraints_set2 = [solver.mkTerm(Kind.EQUAL, course_variable_2, \
	 solver.mkString(course.get("Course_ID")))for course in transcript.get("Courses_Taken", [])]
	constraints_set3 = [solver.mkTerm(Kind.EQUAL, course_variable_3, \
	 solver.mkString(course.get("Course_ID").strip()))for course in transcript.get("Courses_Taken", [])]
	constraints_set4 = [solver.mkTerm(Kind.EQUAL, course_variable_4, \
	 solver.mkString(course.get("Course_ID")))for course in transcript.get("Courses_Taken", [])]
	constraints_set5 = [solver.mkTerm(Kind.EQUAL, course_variable_5, \
	 solver.mkString(course.get("Course_ID").strip()))for course in transcript.get("Courses_Taken", [])]

	constraint_6 = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString('CS103'))
	constraint_7 = solver.mkTerm(Kind.EQUAL, course_variable_1, solver.mkString('CS161'))
	constraints_set8 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course_unit))for course_unit in ['CS109', 'STAT116', 'CME106', 'MS&E220', 'EE178']]
	constraints_set9 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course_unit))for course_unit in ['CS107', 'CSS107E']]
	constraints_set10 = [solver.mkTerm(Kind.EQUAL, course_variable_2, solver.mkString(course_unit))for course_unit in ['CS110', 'CS111']]
 
	constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)
	constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)
	constraint_3 = solver.mkTerm(Kind.OR, *constraints_set3)
	constraint_4 = solver.mkTerm(Kind.OR, *constraints_set4)
	constraint_5 = solver.mkTerm(Kind.OR, *constraints_set5)
	constraint_8 = solver.mkTerm(Kind.OR, *constraints_set8) 
	constraint_9 = solver.mkTerm(Kind.OR, *constraints_set9)
	constraint_10 = solver.mkTerm(Kind.OR, *constraints_set10)

	#area constraint
	formula = solver.mkTerm(Kind.AND, constraint_1, \
	constraint_2, constraint_3, constraint_4, constraint_5, \
	constraint_6, constraint_7, constraint_8, constraint_9, constraint_10)
	print(formula)
	solver.assertFormula(formula)
	result = solver.checkSat()

	# Print the result
	print("Satisfiability:", result)

	# Get and print the model if the formula is satisfiable
	if result.isSat():
		model = solver.getValue(course_variable_1)
		print("Model for course_variable_1:", model)
		model = solver.getValue(course_variable_2)
		print("Model for course_variable_2:", model)
	else: 
		core = solver.getUnsatCore()
		print("Unsat dditional requirement core is: ", core)
    

'''
EXAMPLE 3: 
Total units used to satisfy the Requirements must not exceed 10 units.
'''
def cvc5_example_3():
	solver = solver_init()
	total_units_foundations = sum([course["Earned_Units"] for course in transcript["Courses_Taken"]
				if course["Course_ID"] in ["CS103", "CS109", "Stat116", "CME106", "MS&E220", "EE178", 
								"CS161", "CS107", "CS107E", "CS110", "CS111"]])
	formula = solver.mkTerm(Kind.LEQ, solver.mkInteger(total_units_foundations), solver.mkInteger(10))
	print(formula)
	solver.assertFormula(formula)
	result_checker(solver)
	

'''
EXAMPLE 4: 
One course from the list for Significant Implementation Requirement
'''
def cvc5_example_4():
	solver = solver_init()
	sig_impl_courses = ["CS140", "CS140E", "CS143", "CS144", "CS145", "CS148", "CS151", "CS190", "CS210B", 
			"CS212", "CS221", "CS227B", "CS231N", "CS243", "CS248", "CS248A", "CS341"]
	sig_impl_var = solver.mkConst(solver.getStringSort(), "sig_impl_var")
	sig_impl_constraints = [solver.mkTerm(Kind.EQUAL, sig_impl_var, solver.mkString(course.get("Course_ID")))
				for course in transcript.get("Courses_Taken", [])]
	formula = solver.mkTerm(Kind.OR, *sig_impl_constraints)
	print(formula)
	solver.assertFormula(formula)
	result_checker(solver)

'''
EXAMPLE 5: 
Depth courses must be taken for a letter grade and must be greater than and equal to 21 units
'''
def cvc5_example_5():
	solver = solver_init()
	depth_courses = ["CS221", "CS223A", "CS224N", "CS224S", "CS224U", "CS224V", "CS224W", "CS228", "CS229", "CS231A",
			"CS231N", "CS234", "CS237A", "CS237B", "CS238"]

	depth_var = solver.mkConst(solver.getStringSort(), "depth_var")
	depth_constraints = [
	solver.mkTerm(Kind.EQUAL, depth_var, solver.mkString(course.get('Course_ID')))
	for course in transcript.get('Courses_Taken', [])
	]
	depth_constraint = solver.mkTerm(Kind.OR, *depth_constraints)
	depth_letter_grades = ["A+", "A", "A-", "B+", "B", "B-", "C+", \
         "C", "C-", "D+", "D", "D-", "F"]
	'''
	depth_grade_constraint = solver.mkTerm(Kind.AND, *[
	solver.mkTerm(Kind.EQUAL, solver.mkString(course.get('Grade'))
	for course in transcript.get("Courses_Taken", []) if course.get('Grade') in depth_letter_grades)
	if course["Course_ID"] in depth_courses
	])
 	'''
	depth_units_required = 21
	#missing: "depth grade constraints
	depth_units_constraint = solver.mkTerm(Kind.LEQ,
					solver.mkInteger(sum(course["Earned_Units"]
								for course in transcript["Courses_Taken"]
								if course["Course_ID"] in depth_courses)),
					solver.mkInteger(depth_units_required))

	depth_all_constraints = solver.mkTerm(Kind.AND, depth_constraint, depth_units_constraint)
	solver.assertFormula(depth_all_constraints)
	result_checker(solver)
'''
We should avoid pysmt, because it doesn't support string type 
Bool, Int, Real, BVType, FunctionType, ArrayType
'''
def pysmt_example_1():	
	# Define the courses as string variables
	Course1 = Symbol("Course1", STRING)
	Course2 = Symbol("Course2", STRING)

	# Define the sets of possible courses
	courses_1 = [String("CS 100"), String("CS 101"), String("CS 102")]
	courses_2 = [String("CS 101"), String("CS 102"), String("CS 103")]

	# Define the constraints for Course1 and Course2
	constraint_course1 = Or([EqualsOrIff(Course1, course) for course in courses_1])
	constraint_course2 = Or([EqualsOrIff(Course2, course) for course in courses_2])

	# Constraints that Course1 and Course2 are in the transcript
	constraint_transcript1 = Or([EqualsOrIff(Course1, course.get("Course_ID")) for course in transcript.get("Courses_Taken", [])])
	constraint_transcript2 = Or([EqualsOrIff(Course2, course.get("Course_ID")) for course in transcript.get("Courses_Taken", [])])

	# Combine all constraints
	combined_constraints = And(
	constraint_course1,
	constraint_course2,
	constraint_transcript1,
	constraint_transcript2
	)

	# Get a model that satisfies the constraints
	model = get_model(combined_constraints)

	if model:
		print("A solution exists:")
		print(f"Course1: {model[Course1]}")
		print(f"Course2: {model[Course2]}")
	else:
		print("No solution exists.")

#cvc5_example_1()
#cvc5_example_2()
#cvc5_example_3()
#cvc5_example_4()
cvc5_example_5()

#pysmt_example_1()
