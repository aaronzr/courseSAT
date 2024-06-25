import os
import openai
from PyPDF2 import PdfReader
from openai import OpenAI



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


def translate_to_formal_statements(doc, requirement):
	reader = PdfReader(doc)
	number_of_pages = len(reader.pages)
	text = ""
	for i in range(0, number_of_pages):
		page = reader.pages[i]
		text += page.extract_text()
	extract_prompt = f"""
	Please extract the required courses from {requirement} in the following: {text}.
	Remember, please output every course number in each category and output all course numbers in a single python list [] only.  
	"""

	courses = gpt_infer(extract_prompt)
	print(courses)
	course_file = open(f"{requirement}_course_list.txt", "w+")
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
	solver_file = open(f"{requirement}_solver_statements.py", "w+")
	solver_file.write(solver_statements)

	group_prompt = f"""
	Given a list of required courses {courses} from {requirement} in the following
	document: {text}, please group the required courses in the same category in a bracket () if the category contains
	more than one course and put all grouped courses in 
	a python list. For example, for foundation courses,
	the grouped python list is below:
	[
		cs103,
		cs161,
		(cs107, cs107e),
		(cs110, cs111),
		(cs109, ee178, stat116, cme106, msande220),
	]
	Remember, pleasse output a grouped python list [] only.  
	"""

	grouped_courses = gpt_infer(group_prompt)
	print(grouped_courses)
	filename = requirement + "_grouped_list.py"
	grouped_file = open(filename, 'w+')
	grouped_file.write("course_requirements = " + grouped_courses)

	course_file.close()
	solver_file.close()
	grouped_file.close()

if __name__ == "__main__":
	translate_to_formal_statements(doc="Stanford_AI.pdf", requirement='SIGNIFICANT IMPLEMENTATION REQUIREMENT')

	