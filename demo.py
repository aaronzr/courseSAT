import os
import json
import openai
import subprocess
import chainlit as cl
from PyPDF2 import PdfReader
from openai import OpenAI
from langchain_community.document_loaders import PyPDFLoader, TextLoader
from langchain.text_splitter import RecursiveCharacterTextSplitter
from chainlit.types import AskFileResponse
from schema.requirements_formula import (
	check_breadth,
	check_foundations,
	check_significant_implementation,
	check_artificial_depth,
	check_electives, 
	check_additional)
from schema.process import process, RESULTS_DIR

prior_response = []
requirement_path = "temp1.txt"
transcript_path = "temp2.txt"
TEMP_FILE = "temp_test.py"
text_splitter = RecursiveCharacterTextSplitter(chunk_size=1000, chunk_overlap=100)

def agent_prompt(name, req, transcript_path, trace):
        with open(transcript_path, 'r') as file:
                transcript = json.load(file)
        prompt = f"""
        Your are a semantic parser for transcripts and requirements. Your task is to write a 
        satisfiability script based on a given transcript schema, a given requirement, and a smt unSAT core from checking
        formally experssed requirements. Take the following example output as an example:
        ```
        FoundationCoursesTaken(
        taken_logic_automata_complexity = True,
        logic_course = "CS 103",
        logic_course_units_taken = 4,
        taken_probability = True,
        probablity_course = "CS 109",
        probability_course_units_taken = 3,
        taken_algorithmic_analysis: bool, algorithmic_analysis_course: Enum["CS 161"], algorithmic_analysis_course_units_taken: int, taken_computer_organisation: bool, computer_organisation: Enum["CS 107", "CS 107E"], computer_organisation_course_units_taken: int, taken_principles_of_computer_systems: bool, principles_of_computer_system: Enum["CS110", "CS111"], principles_of_computer_system_course_units_taken: int, confirm_requirements: bool)
        ```
        Suppose a trancript contains some courses satisfying the Foundations Requirement but not all of them. Your task is 
        to fill in whether a sub-constraint of a requirement, e.g. taken_logic_automata_complexity and taken_probability of foundations requirement, is satified with a boolean value, relevant satifying course taken, 
        and course_units_taken. In case sub-constraint such as taken_logic_automata_complexity is satisfied, your output should use the format below:
        ```
        taken_logic_automata_complexity = True,
        logic_course = "CS 103",
        logic_course_units_taken = 4,
        ```
        In case a sub-constraint is not satisfied, use Enum[...] to specify possible courses that can be taken to satisfy the constriant. Using our example output above for unsatisfying sub-constraint, your output should look like the following: 
        ```
        taken_computer_organisation: bool, computer_organisation: Enum["CS 107", "CS 107E"], computer_organisation_course_units_taken: int
        ```
        Putting it together, your output should trictly follow the format below:
        ```
        FoundationCoursesTaken(
        taken_logic_automata_complexity = True,
        logic_course = "CS 103",
        logic_course_units_taken = 4,
        taken_probability = True,
        probablity_course = "CS 109",
        probability_course_units_taken = 3,
        taken_algorithmic_analysis: bool, algorithmic_analysis_course: Enum["CS 161"], algorithmic_analysis_course_units_taken: int, taken_computer_organisation: bool, computer_organisation: Enum["CS 107", "CS 107E"], computer_organisation_course_units_taken: int, taken_principles_of_computer_systems: bool, principles_of_computer_system: Enum["CS110", "CS111"], principles_of_computer_system_course_units_taken: int, confirm_requirements: bool)
        ```
        Given requirement: {req}, transcript: {transcript}, and smt unSAT core: {trace},  please generate a satisfiability python script and fill in the following 
        list similar to the FoundationCoursesTaken(...) format above and output the filled-in list below only:
        ```
        {name.lower()}CourseTaken(
                
        )       
        ```
        """
        output = gpt4_infer(prompt)
        return output

def process_file(file: AskFileResponse):
    if file.type == "text/plain":
        Loader = TextLoader
    elif file.type == "application/pdf":
        Loader = PyPDFLoader

        loader = Loader(file.path)
        documents = loader.load()
        docs = text_splitter.split_documents(documents)
        for i, doc in enumerate(docs):
            doc.metadata["source"] = f"source_{i}"
        return docs


#we need to explicitly tell LLM to fill in none or unknown for Apprval fields.
#Otherwise, it will fill in false
def process_individual_transcript(results_dir, transcript_path):
        transcript = open(transcript_path, "r")
        name = os.path.basename(transcript_path)
        transcript_name, _ = name.split(".")
        prompt = f"""
        Please fill out a json schema template containing Student (student information from the given transcript),
        AP_Credits (Advanced Placement title and Earned Units from the given transcript),
        Courses_Taken (a list of taken courses with relevant course information from the given transcript), 
        Deviations (a list of taken courses deviated from major or specializaion requirements, but can be approved by an advisor to meet a requirement),
        Approval (whether an advior has approved a taken course for degree requirements. This is typically false or unknown from the transcript unless
        otherwise specified), and Cumulativess (cumulative GPA and total units for undnergraduate and graduate degrees) 
        from a given transcript. It's vitally IMPORTANT that you double check and fill in correct information from the given transcript.
        Here is the transcript: {transcript.read()}. Please output a filled transcript json schema in the following format only. Your output MUST strictly follow the format.
        ```
        {{
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
                {{"Term": String, "Course_ID": String, "Title": String, "Earned_Units": Integer, "Grade": String}},
                {{"Term": String, "Course_ID": String, "Title": String, "Earned_Units": Integer, "Grade": String}}, 
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
        Remember, your json schema output should strictly follow the given format above and your json schema output will be read as a ```file``` directly by json.load(file). 
        """
        schema = gpt4_infer(prompt)
        start = "```json"
        start2 = "```python"
        end = "```"
        if start in schema: 
                schema_fix = schema.split(start)[1].split(end)[0]
                if "transcript = " in schema_fix: 
                        schema_fix = schema_fix.replace("transcript =","").strip()
        if start2 in schema: 
                schema_fix = schema.split(start)[1].split(end)[0]
                if "transcript = " in schema_fix: 
                        schema_fix = schema_fix.replace("transcript =","").strip()
        else:
                schema_fix = schema
        if not os.path.exists(results_dir):
                os.makedirs(results_dir)
        file = open(f"{results_dir}/{transcript_name}.json", "w+")
        file.write(schema_fix)  
        file.close()
        print("=================raw model output ======================\n") 
        print(schema_fix)
        print("=======================================\n") 
        path = f"{results_dir}/{transcript_name}.json"
        return path

        
def automated_code_fixer(path, iterations):
        for i in range(iterations):
                cmd = ["python", "schema/schema_test.py", "--t", path]
                process = subprocess.Popen(cmd, 
                           stdout=subprocess.PIPE, 
                           stderr=subprocess.PIPE)

                # wait for the process to terminate
                out, err = process.communicate()
                print(f"out:\n {out}")
                print(f"err:\n {err}")
                errcode = process.returncode
                if "Error" in err.decode("utf-8"):
                        code = open(path, "r")
                        print("We are going to prompt for transcript json schema fix...\n")
                        prompt = f"""
                        You are a bug fixer. Your task is to fix a json file give error messages. You should ONLY make minimal changes to fix the bugs.
                        Please do NOT make the whole file an empty json or modifies the contennt of value fileds.
                        Given the error message {err.decode("utf-8")}, please fix the following json file {code.read()} while
                        preserving the original substance. 
                        """
                        fixed_code =gpt4_infer(prompt)
                        print(f"===============error message=======================\n")
                        print(err.decode("utf-8"))
                        print(f"==============={i} iteration of fixing code=======================\n")
                        start = "```python"
                        start2 = "```json"
                        end = "```"
                        if start in fixed_code: 
                                reformatted_fixed_code = fixed_code.split(start)[1].split(end)[0]
                        if "transcript =" in fixed_code: 
                                reformatted_fixed_code = fixed_code.replace("transcript =","")
                        if start2 in fixed_code: 
                                reformatted_fixed_code = fixed_code.split(start2)[1].split(end)[0]
                        else:
                                reformatted_fixed_code = fixed_code
                        file = open(f"{path}", "w+")
                        file.write(reformatted_fixed_code)
                        file.close()
                else:
                        break
        return path 

def process(transcript_path):
        path = process_individual_transcript(RESULTS_DIR, transcript_path)
        val = automated_code_fixer(path, 30)
        return val

def gpt4_infer(prompt):
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

def gpt3_infer(prompt):
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

def ms_to_smt(requirement_path):
	reqs = ["ELECTIVES", "BREADTH REQUIREMENT", "ARTIFICIAL INTELLEGIENCE DEPTH", "FOUNDATIONS REQUIERMENT",\
		"SIGNIFICANT IMPLEMENTATION REQUIREMENT", "ADDITIONAL REQUIREMENT"]
	req_out = []
	text = open(requirement_path, "r")
	for requirement in reqs: 
		requirement =f"""
			Please extract relevant {requirement} from {text.read()}. Please output 
			extracted requirement of {requirement} in the document only.
			"""
		individual_requirement = gpt3_infer(requirement)
		req_out.append(individual_requirement)
	return reqs, req_out

def automated_formula_fixer(iterations):
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
						fixed_code =gpt4_infer(prompt)
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
		individual_requirement = gpt4o_infer(requirement)
		print(individual_requirement)
		return  individual_requirement


def run_agent(name, req, transcript_path, trace):
	if len(trace)>500:
		short_trace = trace[0:500]
	else:
		short_trace = trace
	policy = agent_prompt(name, req, transcript_path, short_trace)
	print(req)
	start = "```"
	start2 = "```python"
	end = "```"
	if start in policy: 
		fixed_policy = policy.split(start)[1].split(end)[0]
	if start2 in policy: 
		fixed_policy = policy.split(start2)[1].split(end)[0]
	else:
         fixed_policy = policy
	return fixed_policy
			
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
		formula_out = gpt3_infer(formula_prompt)
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
		formula_out = gpt3_infer(formula_prompt)

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
		formula_compile = gpt4_infer(compile_prompt)    
		start = "```python"
		end = "```"
		reformatted_formula_compile = formula_compile.split(start)[1].split(end)[0]
		return reformatted_formula_compile

def run_analysis(transcript_path, requirement_doc):  
	unsat_results = []
	unsat_trace = []
	print("Let's first translate the uploaded document into SMT fomulas...\n") 
	reqs, req_out = ms_to_smt(requirement_doc)
	requirement_dict = dict(zip(reqs, req_out))
	name = os.path.basename(transcript_path)
	transcript_name, _ = name.split(".")
	path = f"{RESULTS_DIR}/{transcript_name}.json"
	transcript = process(transcript_path)
	foundations_result, foundations_trace = check_foundations(transcript)
	breadth_result, breadth_trace = check_breadth(transcript)
	'''
	significant_implementation_result, significant_implementation_trace = check_significant_implementation(transcript)
	depth_result, depth_trace = check_artificial_depth(transcript)
	electives_result, electives_trace = check_electives(transcript)
	additional_result, additional_trace = check_additional(transcript)
	'''
	if foundations_result.isSat()==False:
		unsat_results.append("foundations")
		unsat_trace.append(foundations_trace)
	if breadth_result.isSat()==False:
		unsat_results.append("breadth")
		unsat_trace.append(breadth_trace)
	'''
	if depth_result.isSat()==False:
		unsat_results.append("depth")
		unsat_trace.append(depth_trace)
	if significant_implementation_result.isSat()==False:
		unsat_results.append("significant_implementation")
		unsat_trace.append(significant_implementation_trace)
	if additional_result.isSat()==False:
		unsat_results.append("additional")
		unsat_trace.append(additional_trace)
	if electives_result.isSat()==False:
		unsat_results.append("elective")
		unsat_trace.append(electives_trace)
	'''
	unsat_dict = dict(zip(unsat_results, unsat_trace))
	return unsat_results, requirement_dict, unsat_dict, path

@cl.on_chat_start
async def main():
	requirement = await cl.AskFileMessage(
		content="Please upload a requirement document to begin!", accept=["pdf"]
	).send()

	transcript = await cl.AskFileMessage(
		content="Please also upload a transcript to begin!", accept=["pdf"]
	).send()

	text_0 = process_file(requirement[0])
	print(text_0)
	content1 = ""
	requirement_temp = open(requirement_path, "w+")
	for i in range(len(text_0)):
		content1 += text_0[i].page_content
	requirement_temp.write(content1)
	print("===============bckend_debug=================\n")
	text_1 = process_file(transcript[0])
	print(text_1)
	content2 = ""
	transcript_temp = open(transcript_path, "w+")
	for i in range(len(text_1)):
		content2 += text_1[i].page_content
	transcript_temp.write(content2)
		
	# Let the user know that the system is ready
	await cl.Message(
		content=f"`{requirement[0].name}` uploaded from {requirement[0].path}, it contains {len(text_0)} characters!"
	).send()
				# Let the user know that the system is ready
	await cl.Message(
		content=f"`{transcript[0].name}` uploaded from {transcript[0].path}, it contains {len(text_1)} characters!"
	).send()
	res = await cl.AskActionMessage(
		content="Please select the language if you would like to see CVC5 SMT formulas in a certain language or select 'Final Report' button to see the final analysis report and skip the middle steps",
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
	if res and res.get("value") == "Final":
		await cl.Message(
				content="We are going to generate a final report by running all checks and analysis from the backend...Please type any message to kick off the analysis!",
			).send()
	if res and res.get("value") == "Cancel":
         		await cl.Message(
				content="restarting...",
			).send()			
	print(prior_response)
		
	
@cl.on_message
async def run_translator(message: cl.Message):
	print(prior_response[-1])
	if prior_response[-1] == "Python":
		await cl.Message(
			content=f"analyzing the document and generating python cvc5 formulas now. This might take a while, because we want to ensure correct translation...",
		).send()
		out = await cl.make_async(translate_to_python)(requirement_path, message.content)
		await cl.Message(author="ME", content=f"python solver formulas are: {out}").send()
		await cl.Message(
			content="automatically fixing generated python formula code in 30 iterations...",
		).send()
		response = await cl.make_async(automated_formula_fixer)(30)
		await cl.Message(author="ME", content=response).send()

	print(prior_response[-1])
	if prior_response[-1] == "SMT":
		await cl.Message(
			content="analyzing the document and generating smt cvc5 formulas now...",
		).send()
		response = await cl.make_async(translate_to_smt)(requirement_path, message.content)
		await cl.Message(author="ME", content=response).send()

	if prior_response[-1] == "Final":
		await cl.Message(
			content="analyzing the document and the transcript now...",
		).send()
		unsat_results, requirement_dict, unsat_dict, schema_path = await cl.make_async(run_analysis)(transcript_path, requirement_path)
		transcript = open(schema_path, "r")
		await cl.Message(author="ME", content=f"Here is the translated json schema: {transcript.read()}").send()
		transcript = open(schema_path, "r")
		for i in range(len(unsat_results)): 
			await cl.Message(author="ME", content=f"Here is a list of unsatisfied requirements: {unsat_results[i]}").send()
			await cl.Message(author="ME", content=f"Here is SMT solver core proof for unsatisifed formulas/requirements: {list(unsat_dict.values())[i]}").send()
		await cl.Message(author="ME", content=f"Now we are going to generate agent policies for unsatisfied requirements...").send()
		for i in unsat_results: 
			if i=="foundations":
				f_policy = await cl.make_async(run_agent)("foundations", requirement_dict["FOUNDATIONS REQUIERMENT"], schema_path, unsat_dict["foundations"])
				await cl.Message(author="ME", content=f"Agent policy for unsatified {i} requirement is: {f_policy}").send()
			if i=="breadth":
				b_policy = await cl.make_async(run_agent)("breadth", requirement_dict["BREADTH REQUIREMENT"], schema_path, unsat_dict["breadth"])
				await cl.Message(author="ME", content=f"Agent policy for unsatified {i} requirement is: {b_policy}").send()
			'''
			if i=="significant_implementation":
				e_policy = await cl.make_async(run_agent)("significant_implementation", requirement_dict["SIGNIFICANT IMPLEMENTATION REQUIREMENT"], transcript.read(), unsat_dict['significant_implementation'])
				await cl.Message(author="ME", content=f"Agent policy for unsatified {i} requirement is: {s_policy}").send()
			if i=="depth":
				e_policy = await cl.make_async(run_agent)("depth", requirement_dict["ARTIFICIAL INTELLEGIENCE DEPTH"], transcript.read(), unsat_dict["elective"])
				await cl.Message(author="ME", content=f"Agent policy for unsatified {i} requirement is: {d_policy}").send()
			if i=="elective":
				e_policy = await cl.make_async(run_agent)("elective", requirement_dict["ELECTIVES"], transcript.read(), unsat_dict["elective"])
				await cl.Message(author="ME", content=f"Agent policy for unsatified {i} requirement is: {e_policy}").send()
			if i=="additional":
				a_policy = await cl.make_async(run_agent)("additional", requirement_dict["ADDITIONAL REQUIREMENT"], transcript.read(), unsat_dict["additional"])
				await cl.Message(author="ME", content=f"Agent policy for unsatified {i} requirement is: {a_policy}").send()
			'''
		res = await cl.Message(author="ME", content=f"enter `s` to restart").send()
		if res == 's' or  res == 'S': 
				cl.make_async(main)()