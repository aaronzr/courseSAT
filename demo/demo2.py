import os
import openai
import subprocess
import chainlit as cl
from PyPDF2 import PdfReader
from openai import OpenAI

prior_response = []
file_path = "./temp.txt"
TEMP_FILE = "temp_test.py"
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
	print(doc)
	reader = PdfReader(doc)
	number_of_pages = len(reader.pages)
	text = ""
	for i in range(0, number_of_pages):
		page = reader.pages[i]
		text += page.extract_text()
	return text

def automated_code_fixer(iterations):
		for i in range(iterations):
				cmd = ["python", TEMP_FILE]
				process = subprocess.Popen(cmd, 
						   stdout=subprocess.PIPE, 
						   stderr=subprocess.PIPE)

				# wait for the process to terminate
				out, err = process.communicate()
				print(f"out:\n {out}")
				print(f"err:\n {err}")
				errcode = process.returncode
				if "Error" in err.decode("utf-8"):
						code = open(TEMP_FILE, "r")
						print("We are going to prompt for code fix...\n")
						prompt = f"""
						Given the error message {err.decode("utf-8")}, please fix the following code {code.read()} while
						preserving correct logic.
						"""
						fixed_code =gpt_infer(prompt)
						print(f"===============error message=======================\n")
						print(err)
						print(f"==============={i} iteration of fixing code=======================\n")
						start = "```python"
						end = "```"
						temp = open(TEMP_FILE, "w+")
						reformatted_fixed_code = fixed_code.split(start)[1].split(end)[0]
						temp.write(reformatted_fixed_code)
				else:
						break
		return reformatted_fixed_code
						
   
		
def get_requirement(text_file, requirement):
		text = open(text_file, "r")
		requirement =f"""
		Please extract relevant {requirement} from {text.read()}. Please output 
		extracted requirement of {requirement} in the document only.
		"""
		individual_requirement = gpt_infer(requirement)
		print(individual_requirement)
		return  individual_requirement

        		
def translate_to_smt(requirement_text, requirement): 
		requirement_out = get_requirement(requirement_text, requirement)
		formula_prompt =f"""
		Your task is to generate parameterized cvc5 smt solver formulas for the constraints in each requirement {requirement_out} you have identified.
		be used to satisfy two different requirements.
		```
		(set-logic ALL)

		(declare-const course1 String)
		(declare-const course2 String)

		;; Course1 is \in transcript[*].course
		;; Course2 is \in transcript[*].course
        (and (= course1 course) for course in Transcript.get("Courses_Taken")
        (= course1 course) for course in Transcript.get("Courses_Taken"))


		;; Course1 is in one of (100,101,102)
		;; Course2 is in one of (101, 102, 103)
	
		(and (or(= course1 "CS 100")
		(= course1 "CS 101")
		(= course1 "CS 102"))
		(or(= course2 "CS 101")
		(= course2 "CS 102")
		(= course2 "CS 103")))


		;; The same course cannot be used to satisfy two different requirements:
		 (not (= course1 course2))
		

		;; final formula:
		assert(and (and (and (and (= course1 course) for course in Transcript.get("Courses_Taken")(= course1 course) for course in Transcript.get("Courses_Taken"))(or(= course1 "CS 100")(= course1 "CS 101")(= course1 "CS 102"))(or(= course2 "CS 101")(= course2 "CS 102")(= course2 "CS 103")) (not (= course1 course2)))))
		(check-sat)
		```
		Remember, it's very important that you generate smt formulas that PARAMETRIZE
		course variables to check variables in a given transcript against requirements. Please only generate a
  		giant prameterized formula like the following:  
		```
		(set-logic ALL)

		(declare-const course1 String)
		(declare-const course2 String)
		assert(and (and (and (and (= course1 course) for course in Transcript.get("Courses_Taken")(= course1 course) for course in Transcript.get("Courses_Taken"))(or(= course1 "CS 100")(= course1 "CS 101")(= course1 "CS 102"))(or(= course2 "CS 101")(= course2 "CS 102")(= course2 "CS 103")) (not (= course1 course2)))))
		(check-sat)
		```
		Your task is to generate a parameterized formula reflecting the correct logic of {requirement_out}.
		"""
		formula_out = gpt_infer(formula_prompt)
		start = "```smt"
		end = "```"
		reformatted_formula = formula_out.split(start)[1].split(end)[0]
		return reformatted_formula


def translate_to_python(requirement_text, requirement): 
		requirement_out = get_requirement(requirement_text, requirement)
		formula_prompt =f"""
		Your task is to generate cvc5 python solver formulas for the constraints in each requirement {requirement_out} you have identified.
		Your formulas should include every constraint, including the ones related to advisor approval and deviations.
		The formulas will check satisfiability of a given transcript schema template as input in the following format: 
				```json
		transcript = {{
		"Student": {{
				"Name": String,
				"Program": String, 
				"StudentID": Integer,
				"Coterm": Boolean
		}},
		"AP_Credits": [
				{{"Advanced_Placement": String,
				  "Earned_Units": Integer                   
				}}
		]
		"Courses_Taken": [
				{{"Term": String, "Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}},
				{{"Term": String, "Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}}, 
				...
		]
		"Deviations": [
				{{
				"Deviated_Course_ID": String or "None" when "Approved"==false
				"Approved": Boolean,
				"Approved_By": String or "None" when "Approved"==false,
		}},
		  {{
				"Deviated_Course_ID": String or "None" when "Approved"==false
				"Approved": Boolean,
				"Approved_By": String or "None" when "Approved"==false,
		}},
		]
		"Approval": [
				{{
				"Approved": Boolean,
				"Approved_By": String or "None" when "Approved"==false,
				"Approved_Course_ID": String or "None" when "Approved"==false
		}},
		  {{
				"Approved": Boolean,
				"Approved_By": String or "None" when "Approved"==false,
				"Approved_Course_ID": String or "None" when "Approved"==false
		}},
		]    
		"Cumulatives": {{
				"Undergrad_GPA": Real,
				"Undergrad_Total_Units": Real,
				"Graduate_GPA": Real,
				"Graduate_Total_Units": Real,
		}},
		}}
		```
		Given a transcript schema as input variables, please generate cvc5 smt solver formulas for each constraint in the 
		{requirement_out}. Below is an example formula for a given requiremet: Students must take one of the courses in (CS 100, CS 101, CS 102)
		and one of the courses in (CS 101, CS 102, CS 103). The same course cannot be used to satisfy two different requirements.
		```
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
		solver.assertFormula(formula)
		```
		When generating parameterized cvc5 solver formulas, please instantiate new variables to check the transcript schema against each constraint in the {requirement_out}. You should also include
		solver formulas for advisor approval and deviation constraints if there is one. Please note that your formulas should check taken courses in the transcript against each contraint and requirement. Please generate
		parameterized formulas with respect to the requirements only. 
		"""
		formula_out = gpt_infer(formula_prompt)

		compile_prompt = f"""
		Your task is to convert every lines of python code and relevant comments into
		a compilable format in a template provided to you and write a simple test case to prove correctness. 
		Please format inferred solver fomulas {formula_out} in ```python ....``` to the following compilable format: 
		```
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
										print(f"Model for {{variable}}:", model)
				else: 
						core = solver.getUnsatCore()
						print("Unsat requirement core is: ", core)
				return result

		def function(transcript):
				solver = solver_init()
				
				...#insert inferred formulas and constraint comments here
		``` Please be sure to convert all code and relevnt comments in {formula_out} to the format above and write a transcript schema to
		test code correctness. 
		"""
		formula_compile = gpt_infer(compile_prompt)    
		start = "```python"
		end = "```"
		reformatted_formula_compile = formula_compile.split(start)[1].split(end)[0]
		return reformatted_formula_compile
  
@cl.on_chat_start
async def main():
	files = None
	# Wait for the user to upload a file
	while files == None:
		files = await cl.AskFileMessage(
			content="Please upload a requirement document to begin!", accept=["pdf"]
		).send()
		if files != None: 
			text_file = files[0]
			text = pdf_to_text(text_file.path)
			temp_file = open(file_path, "w+")
			temp_file.write(text)
			# Let the user know that the system is ready
			await cl.Message(
				content=f"`{text_file.name}` uploaded from {text_file.path}, it contains {len(text)} characters!"
			).send()

			res = await cl.AskActionMessage(
				content="Please select the language if you would like to see CVC5 SMT formulas in a certain language or select 'Final Report'\
            				button to see the final analysis report and skip the middle steps",
				actions=[
					cl.Action(name="Click Me!", value="Python", label="✅ Python"),
					cl.Action(name="Click Me!", value="SMT", label="✅ SMT Core"),
					cl.Action(name="Click Me!", value="Final", label="✅ Final Report"),
					cl.Action(name="cancel Me!", value="Cancel", label="❌ Cancel"),
				],
			).send()
		prior_response.append(res.get("value"))
		if res and res.get("value") == "Python":
				await cl.Message(
					content="We are going to generate pythonic CVC5 formulas for your document. Please specify\
					a specific requirement you'd like to translate.",
				).send()
		if res and res.get("value") == "SMT":
				await cl.Message(
					content="We are going to generate SMT CVC5 formulas for your document. Please specify\
					a specific requirement you'd like to translate.",
				).send()
		if res and res.get("value") == "Cancel":
				files = None
		print(prior_response)
		
	
@cl.on_message
async def run_translator(message: cl.Message):
	print(prior_response[-1])
	if prior_response[-1] == "Python":
			await cl.Message(
				content=f"analyzing the document and generating python cvc5 formulas now. This might take a while, because we want to ensure correct translation...",
			).send()
			out = await cl.make_async(translate_to_python)(file_path, message.content)
			await cl.Message(author="ME", content=f"python solver formulas are: {out}").send()
			'''
			await cl.Message(
				content="automatically fixing generated python formula code in 30 iterations...",
			).send()
			response = await cl.make_async(automated_code_fixer)(30)
			await cl.Message(author="ME", content=response).send()
			'''
	print(prior_response[-1])
	if prior_response[-1] == "SMT":
			await cl.Message(
				content="analyzing the document and generating smt cvc5 formulas now...",
			).send()
			response = await cl.make_async(translate_to_smt)(file_path, message.content)
			await cl.Message(author="ME", content=response).send()

	cl.run_sync(main())
