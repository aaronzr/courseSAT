import os
import openai
import requests
from bs4 import BeautifulSoup
from PyPDF2 import PdfReader
from openai import OpenAI

RESULTS_DIR = "../raw_output"
BASELINE_DIR = "../one_shot_baseline"
STANFORD_CS_CORE_WEBLINK = "https://www.cs.stanford.edu/bs-core-requirements"
STANFORD_SENIOR_PROJECT_WEBLINK = "https://www.cs.stanford.edu/bs-requirements-senior-project"

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
		
#granular translation: requirement by requirement precise solver statement translation
def translate_to_formal_statements(doc, requirement):
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

	course_file.close()
	solver_file.close()
	grouped_file.close()
	units_file.close()

def end_to_end_evaluation(transcript_path):
	transcript_name = os.path.basename(transcript_path)
	AI_elective_requirement_path = "/home/sallyjunsongwang/courseSAT/program_sheets/CS_AI_2324PS.pdf"
	AI_MS_requirement_path = "/home/sallyjunsongwang/courseSAT/program_sheets/Stanford_AI_MS.pdf"
	BS_core_requiements = weblink_to_text(STANFORD_CS_CORE_WEBLINK)
	BS_senior_project_requiements = weblink_to_text(STANFORD_SENIOR_PROJECT_WEBLINK)
	BS_AI_elective = pdf_to_text(AI_elective_requirement_path)
	MS_AI = pdf_to_text(AI_MS_requirement_path)
	transcript = pdf_to_text(transcript_path)

	prompt =  f"""
	Your task is to dentify whether a student's transcript, which will be given to you, satisfies specific degree requirements, which will also be given to you. 
 	Please analyze and understand the student transcript: {transcript}, as well as the following BS core requirements: {BS_core_requiements}, 
 	BS senior project requirements: {BS_senior_project_requiements}, BS AI elective requirements: {BS_AI_elective}. If all BS requirements are satisfied,
	please output "BS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript. If  all BS requirements are satisfied, 
	please further analyze and understand the student transcript: {transcript} as well as the MS specialization requirements: {MS_AI}. If all MS requirements are satisfied,
	please output "MS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript.
	"""
	one_shot_answer = gpt_infer(prompt)
	print(one_shot_answer)
	oneshot_file = open(f"{BASELINE_DIR}/{os.path.splitext(transcript_name)[0]}_one_shot.txt", 'w+')
	oneshot_file.write(one_shot_answer)
	oneshot_file.close()

	

if __name__ == "__main__":
	#translate_to_formal_statements(doc="../Stanford_AI.pdf", requirement='SIGNIFICANT IMPLEMENTATION REQUIREMENT')
	transcript = "/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf"
	end_to_end_evaluation(transcript)

	