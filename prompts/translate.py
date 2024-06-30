import os
import openai
import requests
from bs4 import BeautifulSoup
from PyPDF2 import PdfReader
from openai import OpenAI

RESULTS_DIR = "../raw_output2"
STANFORD_CS_CORE_WEBLINK = "https://www.cs.stanford.edu/bs-core-requirements"
STANFORD_SENIOR_PROJECT_WEBLINK = "https://www.cs.stanford.edu/bs-requirements-senior-project"
STANFORD_SOE_SCIENCE_WEBLINK = "https://ughb.stanford.edu/courses/approved-courses/science-courses-2023-24"

def gpt_infer(prompt):
	client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))
	chat_completion = client.chat.completions.create(
			messages=[
					{
					"role": "user",
					"content": f"{prompt}",
					}
			],
			model="gpt-4o",
	)
	return chat_completion.choices[0].message.content

def pdf_to_text(doc):
	reader = PdfReader(doc)
	number_of_pages = len(reader.pages)
	text = ""
	for i in range(0, number_of_pages):
		page = reader.pages[i]
		text += page.extract_text()
	return text

def weblink_to_text(link):
	response = requests.get(link)
	soup = BeautifulSoup(response.text, 'html.parser')
	return soup.text

def get_AI_requirements():
	AI_elective_requirement_path = "/home/sallyjunsongwang/courseSAT/program_sheets/CS_AI_2324PS.pdf"
	AI_MS_requirement_path = "/home/sallyjunsongwang/courseSAT/program_sheets/Stanford_AI_MS.pdf"
	BS_core_requiements = weblink_to_text(STANFORD_CS_CORE_WEBLINK)
	BS_senior_project_requiements = weblink_to_text(STANFORD_SENIOR_PROJECT_WEBLINK)
	BS_AI_elective = pdf_to_text(AI_elective_requirement_path)
	MS_AI = pdf_to_text(AI_MS_requirement_path)
	return BS_core_requiements, BS_AI_elective, BS_senior_project_requiements, MS_AI  

#generate a duo of synthetic transcrpts that satisfy and unsatisfy the BS/MS in CS program 
#count: the desired count of such duo synthetc transcrpts
def llm_synthetic_transcript(transcript_path, count):
	transcript_name = os.path.basename(transcript_path)
	name, _ = transcript_name.split(".")
	transcript = pdf_to_text(transcript_path)
	BS_core_requiements, BS_AI_elective, BS_senior_project_requiements, MS_AI = get_AI_requirements()
	for i in range(count): 
		sat_prompt = f"""
		You will be given a template transcript and course requirements from Stanford University's CS Department. Your job is to generate a new synthetic transcript by
		mutating Name, Student ID, Course Title Attempted, Earned Grade, UG Term GPA, Term Totals, UG Cum GPA, Cum  Totals of each quarter in the transcript and the new synthetic transcript should comply with the given course requirements.
		This is the BS in CS core requirements: {BS_core_requiements}. This is the BS AI elective requirements: {BS_AI_elective}. This is the BS senior project requirements: {BS_senior_project_requiements}.
		This is the MS with AI specializatoin requirements: {MS_AI}. This is the transcript template: {transcript}. 
		The new synthetic transcript MUST comply with provided course requirements. 	You MUST generate a new synthetic transcript only strictly in the same format as the template, nothing else.	
		"""
		sat_transcript = gpt_infer(sat_prompt)
		print(sat_transcript)
		sat_textfile = open(f"../transcripts/LLM_{name}_SAT_{i}.txt", 'w+')
		sat_textfile.write(sat_transcript)
		sat_textfile.close()
		unsat_prompt = f"""
		You will be given a template transcript and course requirements from Stanford University's CS Department. Your job is to generate a new synthetic transcript by
		mutating Name, Student ID, Course Title Attempted, Earned Grade, UG Term GPA, Term Totals, UG Cum GPA, Cum  Totals of each quarter in the transcript and the new synthetic transcript should NOT comply with the given course requirements.
		This is the BS in CS core requirements: {BS_core_requiements}. This is the BS AI elective requirements: {BS_AI_elective}. This is the BS senior project requirements: {BS_senior_project_requiements}.
		This is the MS with AI specializatoin requirements: {MS_AI}. This is the transcript template: {transcript}. 
		The new synthetic transcript MUST NOT comply with provided course requirements. You MUST generate a new synthetic transcript only strictly in the same format as the template, nothing else.	
		"""
		unsat_transcript = gpt_infer(unsat_prompt)
		print(unsat_transcript)
		unsat_textfile = open(f"../transcripts/LLM_{name}_UNSAT_{i}.txt", 'w+')
		unsat_textfile.write(unsat_transcript)
		unsat_textfile.close()
 
 
		
#granular translation: requirement by requirement precise solver statement translation
def translate_masters_to_formal_statements(doc, requirement):
	text = pdf_to_text(doc)
	extract_prompt = f"""
	Please extract the required courses from {requirement} in the following: {text}.
	Remember, please output every course number in each category and output all course numbers in a single python list [] only.  
	"""

	courses = gpt_infer(extract_prompt)
	print(courses)
	course_file = open(f"{RESULTS_DIR}/{requirement}_course_list.txt", "w+")
	course_file.write(courses)
	solver_prompt = f"""
	Given a list of courses {courses}, please translate each course into 
	corresponding cvc5 solver statements. For example, for cs103, you need to generate two python 
	code statements like below: 
	cs103 = solver.mkConst(solver.getBooleanSort(), "CS103")
	cs103_units = solver.mkConst(solver.getIntegerSort(), "CS103_units")
	Please generate compilable solver statements for each course in the list. Please output code only. 
	"""
	solver_statements = gpt_infer(solver_prompt)
	print(solver_statements)
	solver_file = open(f"{RESULTS_DIR}/{requirement}_solver_statements.py", "w+")
	solver_file.write(solver_statements)

	group_prompt = f"""
	Given a list of required courses {courses} from {requirement} in the following
	document: {text}, please group the required courses in the same category in a bracket () if the category contains
	more than one course and put all grouped courses in 
	a python list in lower case and in code without string format. For example, for foundation courses,
	the grouped python list below is okay:
	[
		cs103,
		cs161,
		(cs107, cs107e),
		(cs110, cs111),
		(cs109, ee178, stat116, cme106, msande220),
	]
	The format below is NOT okay: 
	[
		"cs103",
		"cs161",
		("cs107", "cs107e"),
		("cs110", "cs111"),
		("cs109", "ee178", "stat116", "cme106", "msande220"),
	]
	
	Remember, each course should be in lower case in code without string format. Please output a grouped python list [] only.  
	"""
	grouped_courses = gpt_infer(group_prompt)
	print(grouped_courses)
	filename = requirement + "_grouped_list.py"
	grouped_file = open(f"{RESULTS_DIR}/{requirement}_grouped_list.py", 'w+')
	grouped_file.write("course_requirements = " + grouped_courses)
 
	course_unit_prompt = f"""
	Given a list of required courses {courses} from {requirement} in the following
	document: {text}, please put each course in the format of *_units in lower case and in code without string format
	a python list. For example, for foundation courses,
	the python list of course units is below:
	[
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
	Remember, please output a python list [] of course units only.  
	"""
	course_units = gpt_infer(course_unit_prompt)
	print(course_units)
	units_file = open(f"{RESULTS_DIR}/{requirement}__course_unit.py", 'w+')
	units_file.write("course_units = " + course_units)
	if requirement == "ADDITIONAL REQUIREMENTS":
		formula_prompt = f"""
		Your task is to generate python compilable CVC5 solver formulas based on constraints in a course requirements document. 
		Given a list of requirements from {requirement} in the following
		document: {text}. GPT4o has identified the following list of courses for cvc5 formula constraints solving: 
		i) a list of possible courses: {courses}; and ii) course units: {course_units}. Please carefully analyze the units and course requirements in the {requirement} and generate solver formulas in python code
		that check if specified constraints are satisfied accordingly. 
		For example, one such formulaa to check if a list of course 
		```python
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
		```
		Remember, please generate cvc5 formulas in python based on information and {courses} in {requirement}. You must generate cvc5 formulas in python code that meet 
		specified constraints of {requirement} in {text}.
		"""	
	else: 
		formula_prompt = f"""
		Your task is to generate python compilable CVC5 solver formulas based on constraints in a course requirements document. 
		Given a list of required and elective courses {courses} from {requirement} in the following
		document: {text}. GPT4o has identified the following list of courses for cvc5 formula constraints solving: 
		i) a list of courses: {grouped_courses}; and ii) course units: {course_units}. Please carefully analyze the units and course requirements in the {requirement} and generate solver formulas in python code
		that check if specified constraints are satisfied accordingly. You can assume a user input of taken courses in a variable `course_choices` in the following format: 
		```python
  		course_choices = {{
			cs154: [False, 0],
			cs140: [True, 3],
			history244f: [True, 3],
			cs348a: [True, 3]}}
		```
		Given a list of taken course_choices as input, one such formula to check if a list of course satisfies: 
		```python
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
		```
		Remember, please generate cvc5 formulas in python based on {grouped_courses} and {course_units}. You must generate cvc5 formulas in python code that meet 
		specified constraints of {requirement} in {text}.
		"""
	formula_statements = gpt_infer(formula_prompt)
	print(formula_statements)
	formula_file = open(f"{RESULTS_DIR}/{requirement}_solver_formulas.py", "w+")
	formula_file.write(formula_statements)
 
	course_file.close()
	solver_file.close()
	grouped_file.close()
	units_file.close()
	formula_file.close()


#generate a duo of synthetic transcrpts that satisfy and unsatisfy the BS/MS in CS program 
#count: the desired count of such duo synthetc transcrpts
def translate_undergrad_to_formal_statements(doc, requirement):
	SOE_science_courses = weblink_to_text(STANFORD_SOE_SCIENCE_WEBLINK)
	text = pdf_to_text(doc)
	extract_prompt = f"""
	Please extract the required courses from {requirement} in the following: {text}.
	Please pay attention to notes for relevant electives of {requirement} and extract relevant elective courses related to {requirement} too.
	Remember, please output output all course numbers in a single python list [] only.  
	"""

	courses = gpt_infer(extract_prompt)
	print(courses)
	course_file = open(f"{RESULTS_DIR}/{requirement}_course_list.txt", "w+")
	course_file.write(courses)
	solver_prompt = f"""
	Given a list of courses {courses}, please translate each course into 
	corresponding cvc5 solver statements. For example, for cs103, you need to generate two python code statements like below: 
	```python 
	cs103 = solver.mkConst(solver.getBooleanSort(), "CS103")
	cs103_units = solver.mkConst(solver.getIntegerSort(), "CS103_units")
	```
	The course variable should be in lower case. For example cs103, NOT CS103 or CS 103 or CS_103 on the left hand. 
	Please generate compilable solver statements for each course in the list. Please output code only. 
	"""
	solver_statements = gpt_infer(solver_prompt)
	print(solver_statements)
	solver_file = open(f"{RESULTS_DIR}/{requirement}_solver_statements.py", "w+")
	solver_file.write(solver_statements)
	group_prompt = f"""
	Given a list of required and elective courses {courses} from {requirement} in the following
	document: {text} and SOE science elective courses: {SOE_science_courses}, please group the elective courses in the same category in a bracket () if the category contains
	more than one course. If two courses cannot be used to satisfy a requirement at the same time, please group them in the same category. For example, cs157, phil151 should be
	in a single group as (cs157, phil151), because cs157 and phil151 cannot both be used to satisfy the requirements.
 	Please put all grouped courses in a python list in lower case and in code without string format. For example, for mthematics and science requirement,
	the grouped python list below is okay:
	[
		math19,
		math20,
		math21,
		cs103,
		cs109,
		phys41,
		phys43, 
		(math51, math52, math53, math104, math107, math108, math109, math110, math113, cs205l, cme100, cme102, cme104, engr108),
		(cs157, phil151),
	]
	The format below is NOT okay: 
	[
		"math19",
		"math20",
		"math21",
		"cs103",
		"cs109",
		"phys41",
		"phys43", 
		("math51", "math52", "math53", "math104", "math107", "math108", "math109", "math110", "math113", "cs205l", "cme100", "cme102", "cme104", "engr108"),
		("cs157", "phil151"),
	]
	
	Remember, each course should be in lower case in code without string format. Please output a grouped python list [] only.  
	"""
	grouped_courses = gpt_infer(group_prompt)
	print(grouped_courses)
	filename = requirement + "_grouped_list.py"
	grouped_file = open(f"{RESULTS_DIR}/{requirement}_grouped_list.py", 'w+')
	grouped_file.write("course_requirements = " + grouped_courses)
	solver_statements = gpt_infer(solver_prompt)
	print(solver_statements)
	solver_file = open(f"{RESULTS_DIR}/{requirement}_solver_statements.py", "w+")
	solver_file.write(solver_statements)
 
	course_unit_prompt = f"""
	Given a list of required courses {courses} from {requirement} in the following
	document: {text}, please put each course in the format of *_units in lower case and in code without string format
	a python list. For example, for foundation courses,
	the python list of course units is below:
	[
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
	Remember, please output a python list [] of course units only.  
	"""
	course_units = gpt_infer(course_unit_prompt)
	print(course_units)
	units_file = open(f"{RESULTS_DIR}/{requirement}__course_unit.py", 'w+')
	units_file.write("course_units = " + course_units)

	formula_prompt = f"""
	Your task is to generate python compilable CVC5 solver formulas based on constraints in a course requirements document. 
 	Given a list of required and elective courses {courses} from {requirement} in the following
	document: {text} and SOE science elective courses: {SOE_science_courses}, GPT4o has identified the following list of courses for cvc5 formula constraints solving: 
 	i) a list of courses: {grouped_courses}; and ii) course units: {course_units}. Please carefully analyze the units and course requirements in the {requirement} and generate solver formulas in python code
  	that check if specified constraints are satisfied accordingly. You can assume a user input of taken courses in a variable `course_choices` in the following format: 
		```python
  		course_choices = {{
			cs154: [False, 0],
			cs140: [True, 3],
			history244f: [True, 3],
			cs348a: [True, 3]}}
		```
		Given a list of taken course_choices as input, one such formula to check if a list of courses satisfy constraints can be: 
	```python
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
	```
	Remember, please generate cvc5 formulas in python based on {grouped_courses} and {course_units}. You must generate cvc5 formulas in python code that meet 
 	specified constraints of {requirement} in {text}.
	"""
	formula_statements = gpt_infer(formula_prompt)
	print(formula_statements)
	formula_file = open(f"{RESULTS_DIR}/{requirement}_solver_formulas.py", "w+")
	formula_file.write(formula_statements)
 
	course_file.close()
	solver_file.close()
	grouped_file.close()
	units_file.close()
	formula_file.close()

if __name__ == "__main__":
	translate_undergrad_to_formal_statements(doc="../program_sheets/CS_AI_2324PS.pdf", \
	 					requirement="Mathmatics and Science Requirement")
	translate_undergrad_to_formal_statements(doc="../program_sheets/CS_AI_2324PS.pdf", \
	 					requirement="Technology in Society Requirement")
	translate_undergrad_to_formal_statements(doc="../program_sheets/CS_AI_2324PS.pdf", \
	 					requirement="Engineering Fundamentals")
	translate_undergrad_to_formal_statements(doc="../program_sheets/CS_AI_2324PS.pdf", \
	 					requirement="AI Track Core")
	translate_undergrad_to_formal_statements(doc="../program_sheets/CS_AI_2324PS.pdf", \
	 					requirement="AI Track DEPTH")
	translate_undergrad_to_formal_statements(doc="../program_sheets/CS_AI_2324PS.pdf", \
	 					requirement="SENIOR PROJECT")
	translate_masters_to_formal_statements(doc="../program_sheets/Stanford_AI_MS.pdf", \
	 			requirement='SIGNIFICANT IMPLEMENTATION REQUIREMENT')
	translate_masters_to_formal_statements(doc="../program_sheets/Stanford_AI_MS.pdf", \
	 			requirement='BREADTH REQUIREMENT')
	translate_masters_to_formal_statements(doc="../program_sheets/Stanford_AI_MS.pdf", \
	 			requirement='ARTIFICIAL INTELLIGENCE DEPTH REQUIREMENT')
	translate_masters_to_formal_statements(doc="../program_sheets/Stanford_AI_MS.pdf", \
	 			requirement='ELECTIVES')
	translate_masters_to_formal_statements(doc="../program_sheets/Stanford_AI_MS.pdf", \
	 			requirement='ADDITIONAL REQUIREMENTS')
	