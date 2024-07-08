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
                                print(f"Model for {variable}:", model)
	else: 
		core = solver.getUnsatCore()
		print("Unsat dditional requirement core is: ", core)
	return result

def check_artificial_depth(transcript):
        solver = solver_init()
        variables = []

        # 1. All depth courses must be taken for a letter grade* for 3 or more units
        depth_courses = [solver.mkTerm(Kind.AND, 
                        solver.mkTerm(Kind.GEQ, solver.mkInteger(course.get("Earned_Units")), solver.mkInteger(3)),
                        solver.mkTerm(Kind.OR, 
                        solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString('A')),
                        solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString('B')),
                        solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString('C')),
                        solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString('D')),
                        solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Grade")), solver.mkString('F'))
                        )) for course in transcript.get("Courses_Taken", [])]

        # 2. Maximum of 6 units of CS 399 Independent Study
        cs_399_units = sum(course.get("Earned_Units") for course in transcript.get("Courses_Taken", []) if course.get("Course_ID").startswith("CS 399"))
        constraint_cs_399 = solver.mkTerm(Kind.LEQ, solver.mkInteger(cs_399_units), solver.mkInteger(6))

        # 3. One adviser-approved deviation allowed
        approved_deviations = [dev for dev in transcript.get("Deviations", []) if dev.get("Approved")]
        constraint_deviations = solver.mkTerm(Kind.LEQ, solver.mkInteger(len(approved_deviations)), solver.mkInteger(1))

        # 4. Courses taken for your Stanford undergraduate degree do not need to be repeated (not directly checkable here)

        # 5. Specific courses in categories (a) and (b)
        cs_221 = any(course.get("Course_ID") == "CS 221" for course in transcript.get("Courses_Taken", []))
        cs_221_waiver_approved = any(approval.get("Approved_Course_ID") == "CS 221" for approval in transcript.get("Approval", []))
        constraint_cs_221 = solver.mkTerm(Kind.OR, solver.mkBoolean(cs_221), solver.mkBoolean(cs_221_waiver_approved))

        category_b_courses = ["CS 223A", "CS 224N", "CS 224S", "CS 224U", "CS 224V", "CS 224W", "CS 228", 
                        "CS 229", "CS 231A", "CS 231N", "CS 234", "CS 237A", "CS 237B", "CS 238"]
        category_b_taken = [course for course in transcript.get("Courses_Taken", []) if course.get("Course_ID") in category_b_courses]
        constraint_category_b = solver.mkTerm(Kind.GEQ, solver.mkInteger(len(category_b_taken)), solver.mkInteger(4))

        # 6. Total units of at least 21 from categories (a), (b), and (c)
        category_c_courses = ["CS 205L", "CS 224R", "CS 225A", "CS 227B", "CS 229M", "CS 230", "CS 233", "CS 235",
                        "CS 236", "CS 239", "CS 246", "CS 257", "CS 270", "CS 271", "CS 273A", "CS 273B", 
                        "CS 274", "CS 275", "CS 279", "CS 281", "CS 322", "CS 324", "CS 325B", "CS 326",
                        "CS 327A", "CS 329", "CS 330", "CS 331B", "CS 332", "CS 333", "CS 345", "CS 348N", 
                        "CS 361", "CS 368", "CS 371", "CS 375", "CS 377", "CS 379", "CS 398", "CS 399", 
                        "CS 428A", "CS 428B", "CS 432", "EE 263", "EE 276", "EE 278", "EE 364A", "EE 364B", 
                        "EE 377", "EE 378B", "ENGR 205", "ENGR 209A", "MS&E 226", "MS&E 252", "PSYCH 209", 
                        "STATS 202", "STATS 315A", "STATS 315B"]

        all_courses = transcript.get("Courses_Taken", [])
        total_depth_units = sum(course.get("Earned_Units") for course in all_courses
                                if course.get("Course_ID") == "CS 221" or 
                                course.get("Course_ID") in category_b_courses or 
                                course.get("Course_ID") in category_c_courses)

        constraint_total_units = solver.mkTerm(Kind.GEQ, solver.mkInteger(total_depth_units), solver.mkInteger(21))

        # Combine all constraints
        all_constraints = depth_courses + [constraint_cs_399, constraint_deviations, constraint_cs_221, constraint_category_b, constraint_total_units]
        final_formula = solver.mkTerm(Kind.AND, *all_constraints)


        # Create variables
        '''
        required_course = solver.mkConst(solver.getStringSort(), "CS 221")
        required_course_units = solver.mkConst(solver.getIntegerSort(), "required_course_units")
        cs_399_units = solver.mkConst(solver.getIntegerSort(), "cs_399_units")
        total_units = solver.mkConst(solver.getIntegerSort(), "total_units")
        deviation_count = solver.mkConst(solver.getIntegerSort(), "deviation_count")
        advisor_approved = solver.mkConst(solver.getBooleanSort(), "advisor_approved")
        variables.append(required_course)
        # Define list of courses for various categories
        depth_courses = [
        "CS 223A", "CS 224N", "CS 224S", "CS 224U", "CS 224V",
        "CS 224W", "CS 228", "CS 229", "CS 231A", "CS 231N",
        "CS 234", "CS 237A", "CS 237B", "CS 238"
        ]

        additional_courses = [
        "CS 205L", "CS 224R", "CS 225A", "CS 227B", "CS 229M", "CS 230", "CS 233",
        "CS 235", "CS 236", "CS 239", "CS 246", "CS 257", "CS 270", "CS 271", 
        "CS 273A", "CS 273B", "CS 274", "CS 275", "CS 279", "CS 281", "CS 322", 
        "CS 324", "CS 325B", "CS 326", "CS 327A", "CS 329 (any suffix)", "CS 330", 
        "CS 331B", "CS 332", "CS 333", "CS 345", "CS 348N", "CS 361", "CS 368", 
        "CS 371", "CS 375", "CS 377† (any suffix)", "CS 379† (any suffix)", 
        "CS 398", "CS 399†", "CS 428A", "CS 428B", "CS 432", "EE 263", "EE 276", 
        "EE 278", "EE 364A", "EE 364B", "EE 377", "EE 378B", "ENGR 205", "ENGR 209A", 
        "MS&E 226", "MS&E 252", "PSYCH 209", "STATS 202", "STATS 315A", "STATS 315B"
        ]

        # Constraints

        # Constraint 1: Courses must have a letter grade and be for 3 or more units
        transcript_course = solver.mkConst(solver.getStringSort(), "course")
        transcript_units = solver.mkConst(solver.getIntegerSort(), "units") 
        letter_grades = ["A", "B", "C", "D", "E", "F"]
        term_1 = [solver.mkTerm(Kind.EQUAL, transcript_course, solver.mkString(course.get("Grade")))for course in transcript.get("Courses_Taken", [])]
        term_2 = [solver.mkTerm(Kind.EQUAL, transcript_course, solver.mkString(grade))for grade in letter_grades]
        term_3 = [solver.mkTerm(Kind.LEQ, transcript_units, solver.mkInteger(course.get("Earned_Units")))for course in transcript.get("Courses_Taken", [])]
        term_4 = solver.mkTerm(Kind.GEQ, transcript_units, solver.mkInteger(3))        
       
        constraint_1 = solver.mkTerm(Kind.AND, *term_1, *term_2, *term_3, term_4)

        # Constraint 2: At most 6 units of CS 399 Independent Study count towards the depth
        cs_399_constraint = solver.mkTerm(Kind.LEQ, cs_399_units, solver.mkInteger(6))

        # Constraint 3: Any deviations must be noted and approved by an adviser (maximum one deviation)
        deviation_approved_constraints = [
        solver.mkTerm(Kind.AND, solver.mkTerm(Kind.EQUAL, deviation_count, solver.mkInteger(len(transcript.get("Deviations", [])))),
                        solver.mkTerm(Kind.EQUAL, advisor_approved, solver.mkTrue()))
        if len(transcript.get("Deviations", [])) <= 1 else solver.mkFalse()
        ]
        constraint_3 = solver.mkTerm(Kind.AND, *deviation_approved_constraints ) if len(deviation_approved_constraints)>1 else solver.mkFalse()

        # Constraint 4: Courses taken for Stanford undergraduate degree do not need to be repeated

        # Constraint 5: CS 221 requirement
        cs_221_constraints = [
        solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), required_course)
        for course in transcript.get("Courses_Taken", [])
        ]
        cs_221_constraint = solver.mkTerm(Kind.OR, *cs_221_constraints) if len(cs_221_constraints)>1 else solver.mkFalse()

        # Constraint 6: At least 4 of the depth courses must be taken
        #error: syntax

        for depth_course in depth_courses:
                depth_course_constraints = [
                solver.mkTerm(Kind.OR, \
                        [solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), \
                                solver.mkString(depth_course))
                ]) for course in transcript.get("Courses_Taken", [])
                ]
        depth_course_count = solver.mkTerm(Kind.GEQ, solver.mkTerm(Kind.ADD, depth_course_constraints), solver.mkInteger(4))
     
        # Constraint 7: Total units must be at least 21 from categories (a), (b), and (c)
        all_courses = depth_courses + additional_courses
        total_units_constraints = [
        solver.mkTerm(Kind.OR, solver.mkTerm(Kind.EQUAL, solver.mkString(course.get("Course_ID")), solver.mkString(course_id)))
        for course_id in all_courses
        for course in transcript.get("Courses_Taken", [])
        ]
        total_units_sum = solver.mkTerm(Kind.ADD, *total_units_constraints)
        total_units_constraint = solver.mkTerm(Kind.GEQ, total_units_sum, solver.mkInteger(21))

        # Combine all constraints
        final_constraints = solver.mkTerm(
        Kind.AND,
        constraint_1,
        cs_399_constraint,
        constraint_3,
        cs_221_constraint,
        depth_course_count,
        total_units_constraint
        )

        # Assert the final constraints
        solver.assertFormula(final_constraints)
        '''
        print(final_formula)
        solver.assertFormula(final_formula)    
        result = result_checker(solver, variables)
        return result
        
if __name__ == "__main__":
	schema_path = "../schema_results/stanford_transcript1.json"
	with open(schema_path, 'r') as file:
		transcript = json.load(file)
	check_artificial_depth(transcript)