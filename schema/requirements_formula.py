import os
import re
import sys
import cvc5
import json
from cvc5 import Kind
from test import *

def solver_init(): 
	solver = cvc5.Solver()
	solver.setOption("produce-unsat-cores", "true")
	solver.setOption("produce-models", "true")
	solver.setLogic("ALL")
	return solver 


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

def check_breadth(transcript_path):
	solver = solver_init()
	with open(transcript_path, 'r') as file:
		transcript = json.load(file)
    
	# Create course variables for the three breadth requirements
	course_a = solver.mkConst(solver.getStringSort(), "course_a")
	course_b = solver.mkConst(solver.getStringSort(), "course_b")
	course_c = solver.mkConst(solver.getStringSort(), "course_c")

	# Check that the courses are unique and from different areas
	constraints_set1 = []
	constraints_set2 = []
	constraints_set3 = []

	for course in transcript.get("Courses_Taken", []):
		constraints_set1.append(solver.mkTerm(Kind.EQUAL, course_a, solver.mkString(str(course.get("Course_ID")))))
		constraints_set2.append(solver.mkTerm(Kind.EQUAL, course_b, solver.mkString(str(course.get("Course_ID")))))
		constraints_set3.append(solver.mkTerm(Kind.EQUAL, course_c, solver.mkString(str(course.get("Course_ID")))))

	constraint1 = solver.mkTerm(Kind.OR, *constraints_set1)
	constraint2 = solver.mkTerm(Kind.OR, *constraints_set2)
	constraint3 = solver.mkTerm(Kind.OR, *constraints_set3)

	# Constraint for at least 3 units per course
	units_constraints = []
	for course in transcript.get("Courses_Taken", []):
		if course["Earned_Units"] >= 3:
			units_constraints.append(solver.mkTrue())
		else:
			units_constraints.append(solver.mkFalse())
    
	units_constraints_combined = solver.mkTerm(Kind.AND, *units_constraints)

	# Constraint for letter grade
	grade_constraints = []
	letters = ["A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "F"]
	for course in transcript.get("Courses_Taken", []):
		if course["Grade"] in letters:
			grade_constraints.append(solver.mkTrue())
		else:
			grade_constraints.append(solver.mkFalse())

	grade_constraints_combined = solver.mkTerm(Kind.AND, *grade_constraints)

	# Constraints for courses from different areas
	area_a_courses = ["CS 154", "CS 157", "CS 168", "CS 254", "CS 261", "CS 265", "EE 364A", "EE 364B", "Phil 251"]
	area_b_courses = ["CS 140", "CS 140E", "CS 143", "CS 144", "CS 149", "CS 212", "CS 242", "CS 243", "CS 244", "CS 244B", "CS 295", "CS 316", "CS 358", "EE 180", "EE 282", "EE 382E"]
	area_c_courses = ["CS 145", "CS 147", "CS 148", "CS 155", "CS 173", "CS 221", "CS 223A", "CS 224N", "CS 224U", "CS 224W", "CS 227B", "CS 228", "CS 229", "CS 229M", "CS 231A", "CS 231N", "CS 234", "CS 236", "CS 237A", "CS 245", "CS 246", "CS 247", "CS 248", "CS 248A", "CS 251", "CS 255", "CS 273A", "CS 273B", "CS 279", "CS 345", "CS 347", "CS 348A", "CS 348B", "CS 348C", "CS 348E", "CS 348I", "CS 348K", "CS 355", "CS 356", "CS 373"]
	area_d_courses = ["CS 152", "CS 181", "CS 182", "CS 256", "CS 281", "CS 329T", "CS 384", "AMSTUD 133", "AMSTUD 145", "ANTHRO 132D", "COMM 118S", "COMM 120W", "COMM 124", "COMM 130D", "COMM 145", "COMM 154", "COMM 166", "COMM 186W", "COMM 230A", "COMM 230B", "COMM 230C", "DESINST 215", "DESINST 240", "EARTHSYS 213", "ENGLISH 184D", "ENGR 248", "HISTORY 244F", "INTLPOL 268", "LAW 4039", "ME 177", "MS&E 193", "MS&E 231", "MS&E 234", "MS&E 254", "POLISCI 150A", "PSYCH 215", "PUBLPOL 103F", "PUBLPOL 353B"]

	constraints_set_a = [solver.mkTerm(Kind.EQUAL, course_a, solver.mkString(course)) for course in area_a_courses]
	constraints_set_b = [solver.mkTerm(Kind.EQUAL, course_b, solver.mkString(course)) for course in area_b_courses]
	constraints_set_c = [solver.mkTerm(Kind.EQUAL, course_c, solver.mkString(course)) for course in area_c_courses]

	constraint_area_a = solver.mkTerm(Kind.OR, *constraints_set_a)
	constraint_area_b = solver.mkTerm(Kind.OR, *constraints_set_b)
	constraint_area_c = solver.mkTerm(Kind.OR, *constraints_set_c)

	# Combine all the constraints
	formula = solver.mkTerm(
		Kind.AND,
		constraint1,
		constraint2,
		constraint3,
		units_constraints_combined,
		grade_constraints_combined,
		solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_a, course_b)),  # courses must be different
		solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_a, course_c)),
		solver.mkTerm(Kind.NOT, solver.mkTerm(Kind.EQUAL, course_b, course_c)),
		solver.mkTerm(Kind.OR, constraint_area_a, constraint_area_b, constraint_area_c)
	)

	solver.assertFormula(formula)
	result, trace = result_checker(solver, [course_a, course_b, course_c])
	return result, trace
    
def check_significant_implementation(transcript_path):
	with open(transcript_path, 'r') as file:
		transcript = json.load(file)
	solver = solver_init()

	# Define the course list that satisfies the significant implementation requirement
	significant_implementation_courses = ['CS 140', 'CS 140E', 'CS 143', 'CS 144', 'CS 145', 'CS 148', 'CS 151', 
					  'CS 190', 'CS 210B', 'CS 212', 'CS 221', 'CS 227B', 'CS 231N', 
					  'CS 243', 'CS 248 / 248A', 'CS 341']

	# Define the variables for the solver
	course_variable = solver.mkConst(solver.getStringSort(), "course")
	grade_variable = solver.mkConst(solver.getStringSort(), "grade")
	stanford_variable = solver.mkConst(solver.getBooleanSort(), "stanford")

	# Constraint: course in significant_implementation_courses
	constraints_set1 = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course)) for course in significant_implementation_courses]
	constraint_1 = solver.mkTerm(Kind.OR, *constraints_set1)

	# Constraint: course taken for a letter grade ('A', 'B', 'C', 'D', 'F')
	letter_grades = ['A', 'B', 'C', 'D', 'F']
	constraints_set2 = [solver.mkTerm(Kind.EQUAL, grade_variable, solver.mkString(grade)) for grade in letter_grades]
	constraint_2 = solver.mkTerm(Kind.OR, *constraints_set2)

	# Constraint: course taken at Stanford
	constraint_3 = solver.mkTerm(Kind.EQUAL, stanford_variable, solver.mkBoolean(True))

	# Combining the constraints
	general_constraints = solver.mkTerm(Kind.AND, constraint_1, constraint_2, constraint_3)

	# Check the transcript for the constraints
	transcript_constraints = []
	for course in transcript.get("Courses_Taken", []):
		course_constraints = [solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(str(course["Course_ID"])))]
		course_constraints.append(solver.mkTerm(Kind.EQUAL, grade_variable, solver.mkString(str(course["Grade"]))))
		course_constraints.append(solver.mkTerm(Kind.EQUAL, stanford_variable, solver.mkBoolean(course.get("Taken_At_Stanford", False))))

		transcript_constraints.append(solver.mkTerm(Kind.AND, *course_constraints))

	significant_course_constraint = solver.mkTerm(Kind.OR, *transcript_constraints)
	final_constraint = solver.mkTerm(Kind.AND, general_constraints, significant_course_constraint)

	# Handling coterm students who took equivalent courses as undergraduates
	if transcript["Student"]["Coterm"]:
		undergrad_credits_constraints = []
		for course in transcript.get("Courses_Taken", []):
			if any(sub in course["Title"] for sub in significant_implementation_courses):
				undergrad_credits_constraints.append(solver.mkTerm(Kind.EQUAL, course_variable, solver.mkString(course["Course_ID"])))

		#undergrad_credits_constraint = solver.mkTerm(Kind.OR, undergrad_credits_constraints)
		final_constraint = solver.mkTerm(Kind.OR, *final_constraint, *undergrad_credits_constraints)

	# Handling approved deviations
	deviation_constraints = []
	for deviation in transcript.get("Deviations", []):
		if deviation["Approved"]:
			is_approved_by_cynthia = solver.mkTerm(Kind.EQUAL, solver.mkString(deviation["Approved_By"]), solver.mkString("Cynthia Lee"))
			deviation_constraints.append(is_approved_by_cynthia)

	if deviation_constraints:
		deviation_constraint = solver.mkTerm(Kind.AND, *deviation_constraints)
		final_constraint = solver.mkTerm(Kind.OR, final_constraint, deviation_constraint)

	solver.assertFormula(final_constraint)
	result, trace = result_checker(solver, [course_variable, grade_variable, stanford_variable])
	# Check satisfiability
	return result, trace


def check_foundations(transcript_path):
	with open(transcript_path, 'r') as file:
		transcript = json.load(file)
	solver = solver_init()
	# Helper Function to Assert Course Constraints
	def course_constraint(course_title, valid_titles):
		course_var = solver.mkConst(solver.getStringSort(), course_title)
		constraints = [solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(str(course["Course_ID"]))) for course in transcript.get("Courses_Taken", [])]
		if len(constraints) == 0:
			return solver.mkFalse(), course_var
		elif len(constraints) == 1:
			return constraints[0], course_var
		else:
			return solver.mkTerm(Kind.OR, *constraints), course_var

	# List the required courses and their equivalent titles
	required_courses = {
	"Logic, Automata & Complexity": ["CS103"],
	"Probability": ["CS109", "Stat116", "CME106", "MS&E220", "EE178"],
	"Algorithmic Analysis": ["CS161"],
	"Computer Organ & Sys": ["CS107", "CS107E"],
	"Principles of Computer Systems": ["CS110", "CS111"],
	}

	course_vars = {}
	course_constraints = []
	for course_title, valid_titles in required_courses.items():
		constraint, course_var = course_constraint(course_title, valid_titles)
		course_constraints.append(constraint)
		course_vars[course_title] = course_var

	# Combine all course constraints
	if len(course_constraints) == 1:
		all_course_constraints = course_constraints[0]
	else:
		all_course_constraints = solver.mkTerm(Kind.AND, *course_constraints)

	# Constraint to check that total units do not exceed 10 units
	total_units_var = solver.mkConst(solver.getRealSort(), "total_units")
	all_units = [solver.mkReal(course["Earned_Units"]) for course in transcript.get("Courses_Taken", [])]

	# Sum of units calculation
	if len(all_units) > 1:
		overall_units_sum = solver.mkTerm(Kind.ADD, *all_units)
	elif len(all_units) == 1:
		overall_units_sum = all_units[0]
	else:
		overall_units_sum = solver.mkReal(0)

	# Sum of units constraint
	sum_units_constraint = solver.mkTerm(Kind.LEQ, overall_units_sum, solver.mkReal(10))

	# Combine all constraints
	overall_constraint = solver.mkTerm(Kind.AND, all_course_constraints, sum_units_constraint)

	# Check for advisor approval on deviations
	def advisor_approval_constraint():
		approval_constraints = []
		for approval in transcript.get("Approval", []):
			is_approved = solver.mkBoolean(approval["Approved"])
			if is_approved:
				approval_constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkString(approval["Approved_Course_ID"]), solver.mkString("CS103")))  # Example
		if len(approval_constraints) > 1:
			return solver.mkTerm(Kind.AND, *approval_constraints)
		elif len(approval_constraints) == 1:
			return approval_constraints[0]
		return solver.mkTrue()

	# Get the final approval constraint
	final_approval_constraint = advisor_approval_constraint()

	# Add approval constraints to the overall constraint
	final_constraint = solver.mkTerm(Kind.AND, overall_constraint, final_approval_constraint)

	# Assert the final constraint to the solver
	print(final_constraint)
	solver.assertFormula(final_constraint)

	# Check satisfiability and return the result
	result, trace = result_checker(solver, list(course_vars.values()))
	return result, trace

def check_artificial_depth(transcript_path):
	with open(transcript_path, 'r') as file:
		transcript = json.load(file)
	solver = solver_init()
	variables = []

	# Variables
	courses_taken = transcript.get("Courses_Taken", [])
	deviations = transcript.get("Deviations", [])
	approval = transcript.get("Approval", [])

	courses_taken_vars = [solver.mkConst(solver.getStringSort(), f"course{i}") for i in range(len(courses_taken))]
	units_taken_vars = [solver.mkConst(solver.getRealSort(), f"units{i}") for i in range(len(courses_taken))]
	grades_taken_vars = [solver.mkConst(solver.getStringSort(), f"grade{i}") for i in range(len(courses_taken))]
	variables = courses_taken_vars + units_taken_vars + grades_taken_vars
	# All courses must be taken for a letter grade for 3 or more units
	letter_grades = ["A", "B", "C", "D", "E", "F"]
	# Create constraints to ensure all courses are taken for a letter grade
	all_grades_constraints = [
	solver.mkTerm(Kind.OR, *[solver.mkTerm(Kind.EQUAL, grade_var, solver.mkString(grade)) for grade in letter_grades])
	for grade_var in grades_taken_vars
	]

	# Create constraints to ensure all courses are taken for 3 or more units
	all_units_constraints = [solver.mkTerm(Kind.GEQ, unit_var, solver.mkReal(3)) for unit_var in units_taken_vars]


	# A maximum of 6 units of CS 399 Independent Study may be counted towards the depth
	# A maximum of 6 units of CS 399 Independent Study may be counted towards the depth
	cs_399_units = [
	solver.mkTerm(
		Kind.ITE, 
		solver.mkTerm(Kind.EQUAL, course_var, solver.mkString("CS 399")), 
		unit_var, 
		solver.mkReal(0)
	) 
	for course_var, unit_var in zip(courses_taken_vars, units_taken_vars)
	]

	cs_399_units_total = solver.mkTerm(Kind.ADD, *cs_399_units)

	# Ensure that at most 6 units of CS 399 are counted
	cs_399_constraint = solver.mkTerm(Kind.LEQ, cs_399_units_total, solver.mkReal(6))

	# Maximum of one advisor-approved deviation allowed
	approved_deviations = [
		solver.mkTerm(
			Kind.ITE, 
			solver.mkTerm(Kind.EQUAL, solver.mkBoolean(d.get("Approved")), solver.mkBoolean(True)), 
			solver.mkInteger(1), 
			solver.mkInteger(0)
		) 
		for d in deviations
	]

	approved_deviations_total = len(approved_deviations)

	# Ensure that at most 1 approved deviation is allowed
	approved_deviations_constraint = solver.mkTerm(Kind.LEQ, solver.mkInteger(approved_deviations_total), solver.mkInteger(1))
	# Check if CS 221 is taken or the deviation is approved
	cs_221_constraints = [
	solver.mkTerm(Kind.EQUAL, course_var, solver.mkString("CS 221")) 
	for course_var in courses_taken_vars
	]

	cs_221_approved = [
	solver.mkTerm(Kind.EQUAL, solver.mkString(d.get("Deviated_Course_ID")), solver.mkString("CS 221")) 
	for d in deviations if d.get("Approved")
	]

	# Combine the constraints to check if CS 221 is taken or approved as a deviation
	if cs_221_approved:
		cs_221_waived_approved = solver.mkTerm(Kind.OR, *cs_221_approved)
		cs_221_constraint = solver.mkTerm(Kind.OR, solver.mkTerm(Kind.OR, *cs_221_constraints), cs_221_waived_approved)
	else:
		cs_221_constraint = solver.mkTerm(Kind.OR, *cs_221_constraints)

	# At least four of the specific courses must be taken
	depth_courses = ["CS 223A", "CS 224N", "CS 224S", "CS 224U", "CS 224V", "CS 224W", "CS 228", "CS 229",
			"CS 231A", "CS 231N", "CS 234", "CS 237A", "CS 237B", "CS 238"]
	depth_courses_constraints = [
	solver.mkTerm(
		Kind.ITE, 
		solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(course)), 
		solver.mkInteger(1), 
		solver.mkInteger(0)
	) 
	for course_var in courses_taken_vars 
	for course in depth_courses
	]

	depth_courses_sum = solver.mkTerm(Kind.ADD, *depth_courses_constraints)

	# Ensure at least four of the depth courses are taken
	four_depth_courses_requirement = solver.mkTerm(Kind.GEQ, depth_courses_sum, solver.mkInteger(4))

	# Minimum of 21 units from the categories (a), (b), and additional approved courses
	all_courses = depth_courses + [
	"CS 205L", "CS 224R", "CS 225A", "CS 227B", "CS 229M", "CS 230", "CS 233", "CS 235",
	"CS 236", "CS 239", "CS 246", "CS 257", "CS 270", "CS 271", "CS 273A", "CS 273B", "CS 274",
	"CS 275", "CS 279", "CS 281", "CS 322", "CS 324", "CS 325B", "CS 326", "CS 327A", "CS 329",
	"CS 330", "CS 331B", "CS 332", "CS 333", "CS 345", "CS 348N", "CS 361", "CS 368", "CS 371",
	"CS 375", "CS 377", "CS 379", "CS 398", "CS 399", "CS 428A", "CS 428B", "CS 432", "EE 263", "EE 276",
	"EE 278", "EE 364A", "EE 364B", "EE 377", "EE 378B", "ENGR 205", "ENGR 209A", "MS&E 226", "MS&E 252",
	"PSYCH 209", "STATS 202", "STATS 315A", "STATS 315B"
	]
	# Ensure units are correctly paired with the course variables
	units_approved_courses = [
	solver.mkTerm(
		Kind.ITE,
		solver.mkTerm(Kind.EQUAL, course_var, solver.mkString(course)),
		unit_var,
		solver.mkReal(0)
	)
	for course_var, unit_var in zip(courses_taken_vars, units_taken_vars)
	for course in all_courses
	]

	units_total_approved_courses = solver.mkTerm(Kind.ADD, *units_approved_courses)
	units_constraint = solver.mkTerm(Kind.GEQ, units_total_approved_courses, solver.mkReal(21))


	# Combining all the constraints
	final_constraints = [
	*all_grades_constraints, 
	*all_units_constraints, 
	cs_399_constraint, 
	approved_deviations_constraint, 
	cs_221_constraint, 
	four_depth_courses_requirement, 
	units_constraint
	]
	final_formula = solver.mkTerm(Kind.AND, *final_constraints)
	# Assert the final formula
	solver.assertFormula(final_formula)
	result, trace = result_checker(solver, variables)
	return result, trace

def check_electives(transcript_path):
	with open(transcript_path, 'r') as file:
		transcript = json.load(file)
	solver = solver_init()
	variables = []

	def check_digit(inputString):
		count = 0
		for char in inputString:
			if char.isdigit(): 
				count += 1
		if count == len(inputString):
			return True
		return False
	
	# Define constraints within this function using the provided transcript schema
	def add_constraints(solver, transcript):
		constraints_set1 = []
		for course in transcript["Courses_Taken"]: 
			if check_digit(course["Course_ID"].split()[1][0:2]):
			# Constraint: All courses submitted for the MSCS degree must be numbered 100 or greater.
				constraints_set1.append(solver.mkTerm(
					Kind.GEQ, 
					solver.mkReal(int(course["Course_ID"].split()[1][0:2])),
					solver.mkReal(100)
				))
		constraint_1 = solver.mkTerm(Kind.AND, *constraints_set1)
		solver.assertFormula(constraint_1)
		
		# Constraint: At most 10 units of Foundations requirement courses may be counted toward 45 units.
		max_foundation_units = 10
		foundation_courses = []  # Assume foundation courses are identified, add logic if necessary
		foundation_units_sum = sum([course["Earned_Units"] for course in foundation_courses])
		foundation_constraint = solver.mkTerm(
			Kind.LEQ,
			solver.mkReal(foundation_units_sum),
			solver.mkReal(max_foundation_units)
		)
		solver.assertFormula(foundation_constraint)
		
		# Constraint: At most 3 units of 1-2 unit seminars may be counted toward 45 units.
		seminar_courses = [course for course in transcript["Courses_Taken"] if 1 <= course["Earned_Units"] <= 2]
		seminar_units_sum = sum([course["Earned_Units"] for course in seminar_courses])
		seminar_constraint = solver.mkTerm(
			Kind.LEQ,
			solver.mkReal(seminar_units_sum),
			solver.mkReal(3)
		)
		solver.assertFormula(seminar_constraint)

		# Constraint: At least 36 units must be taken for a letter grade (or CR or S in specified terms)
		letter_grade_units_min = 36
		letter_grades = ['A+', 'A', 'A-', 'B+', 'B', 'B-', 'C+', 'C', 'C-', 'D+', 'D', 'D-', 'F']  # Add 'CR' and 'S' for specific terms (Spring 19-20 and Fall-Summer 20-21)
		letter_grade_courses = [course for course in transcript["Courses_Taken"] if course["Grade"] in letter_grades]
		letter_grade_units_sum = sum([course["Earned_Units"] for course in letter_grade_courses])
		letter_grade_constraint = solver.mkTerm(
			Kind.GEQ,
			solver.mkReal(letter_grade_units_sum),
			solver.mkReal(letter_grade_units_min)
		)
		solver.assertFormula(letter_grade_constraint)

		# Constraint: Average grade must be at least B (3.0 in Stanford’s GPA scale)
		total_units = sum([course["Earned_Units"] for course in transcript["Courses_Taken"]])
		earned_grade_points = {
			'A+': 4.3, 'A': 4.0, 'A-': 3.7, 'B+': 3.3, 'B': 3.0, 'B-': 2.7, 'C+': 2.3,  'C-': 1.7, 'D': 1.0, 'F': 0.0,
			'CR': 3.0, 'S': 3.0  # Assuming specific CR/S terms as 3.0 for computational convenience
		}
		grade_points_sum = sum([earned_grade_points[course["Grade"]] * course["Earned_Units"] for course in transcript["Courses_Taken"] if course["Grade"] in earned_grade_points])
		average_grade = grade_points_sum / total_units
		grade_constraint = solver.mkTerm(
			Kind.GEQ,
			solver.mkReal(average_grade),
			solver.mkReal(3.0)
		)
		solver.assertFormula(grade_constraint)

		# Constraint: Units previously applied toward BS requirements may not also be counted toward the MSCS.
		bs_units = 0  # To be dynamically checked or estimated in a real scenario.
		ms_units_constraint = solver.mkTerm(
			Kind.EQUAL,
			solver.mkReal(bs_units),
			solver.mkReal(0)
		)
		solver.assertFormula(ms_units_constraint)

		# Constraint: At least 45 graduate units at Stanford are required for the MSCS degree
		grad_units_min = 45
		total_units_earned = sum([course["Earned_Units"] for course in transcript["Courses_Taken"]])
		grad_units_constraint = solver.mkTerm(
			Kind.GEQ,
			solver.mkReal(total_units_earned),
			solver.mkReal(grad_units_min)
		)
		solver.assertFormula(grad_units_constraint)

		# Constraints for electives and advisor approval
		cs_courses = ["CS196", "CS198", "CS390A", "CS390B", "CS390C"]
		advisor_approval = transcript["Approval"]
		deviations = transcript["Deviations"]
		for course in transcript["Courses_Taken"]:
			advisor_constraints = []
			if course["Course_ID"] in cs_courses:
				advisor_constraints.append(any(solver.mkBoolean(bool(a["Approved"]))for a in advisor_approval if a["Approved_Course_ID"] == course["Course_ID"]))
			for dev in deviations:
				if dev["Deviated_Course_ID"] == course["Course_ID"] and dev["Approved"]:
					advisor_constraints.append(solver.mkBoolean(True))
			advisor_constraint = solver.mkTerm(Kind.AND, *advisor_constraints) if advisor_constraints else solver.mkBoolean(True)
			solver.assertFormula(advisor_constraint)

	# Add constraints to the solver based on the transcript
	add_constraints(solver, transcript)
	
	# Check the satisfiability and print the result
	result, trace = result_checker(solver, variables)
	return result, trace

def check_additional(transcript_path):
	with open(transcript_path, 'r') as file:
		transcript = json.load(file)
	solver = solver_init()
	vars = []
	# Requirement 
	course_ids = [
		solver.mkConst(solver.getIntegerSort(), f"course_id_{i}")
		for i, course in enumerate(transcript.get("Courses_Taken", []))
	]
	vars.append(course_ids)
	constraints_set = [
		solver.mkTerm(Kind.GEQ, course_id, solver.mkInteger(100))
		for course_id in course_ids
	]
	requirement_1 = solver.mkTerm(Kind.AND, *constraints_set)
	foundations_courses =["CS103", "CS109", "Stat116", "CME106", "MS&E220", "EE178",\
		"CS161", "CS107", "CS107E", "CS110", "CS111"]
	# Requirement 2: At most 10 units of Foundations requirement courses.
	foundations_units = 0
	for course in transcript.get("Courses_Taken", []):
		if course["Course_ID"].strip() in foundations_courses: 
			foundations_units += course["Earned_Units"]
          
	requirement_2 = solver.mkTerm(Kind.LEQ, solver.mkInteger(foundations_units), solver.mkInteger(10))

	# Requirement 3: At most 3 units of 1-2 unit seminars.
	seminar_units = sum(
		course["Earned_Units"] for course in transcript.get("Courses_Taken", [])
		if 1 <= course["Earned_Units"] <= 2
	)
	requirement_3 = solver.mkTerm(Kind.LEQ, solver.mkInteger(seminar_units), solver.mkInteger(3))

	# Requirement 4: At least 36 units for a letter grade.
	courses_letter_grade = [
		course for course in transcript.get("Courses_Taken", []) if course["Grade"] not in ["CR", "S"]
	]
	# Add courses satisfying the exception for Spring 19-20 through Summer 20-21
	courses_cr_s_in_exception = []
	for course in transcript.get("Courses_Taken", []):
		if course["Grade"] in ["CR", "S"] and "2019-2020 Spring" in course.get("Term") or "2020-2021 Summer" in course.get("Term"):
			courses_cr_s_in_exception.append(course)
	letter_grade_units = sum(
         course["Earned_Units"] for course in courses_letter_grade + courses_cr_s_in_exception
	)
	requirement_4 = solver.mkTerm(Kind.GEQ, solver.mkInteger(letter_grade_units), solver.mkInteger(36))

	# Requirement 5: Average grade must be at least 3.0.
	requirement_5 = solver.mkTerm(Kind.GEQ, solver.mkReal(transcript.get("Cumulatives").get("Graduate_GPA")), solver.mkReal(3.0))

	# Requirement 6: Units applied toward BS may not count toward MSCS.
	#TODO: maybe asking for user input instead

	# Requirement 7: At least 45 graduate units at Stanford.
	requirement_6 = solver.mkTerm(Kind.GEQ, solver.mkReal(transcript.get("Cumulatives").get("Graduate_Total_Units")), solver.mkReal(45))

	# Combine all requirements
	final_formula = solver.mkTerm(Kind.AND, requirement_1, requirement_2, requirement_3, requirement_4, requirement_5, requirement_6)
	solver.assertFormula(final_formula)
	result, trace = result_checker(solver, vars)

	return result, trace
		
if __name__ == "__main__":
	schema_path = "../schema_results/stanford_transcript1.json"
	#with open(schema_path, "r") as file: 
	#	transcript = json.load(file)
	
 
	#result = check_foundations(transcript)
	result, _ = check_additional(schema_path)
	#result = check_significant_implementation(transcript)
	#result, trace = check_breadth(schema_path)
	#print(result)
	#check_artificial_depth(transcript_depth_test)