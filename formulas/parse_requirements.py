import os
import openai
import requests
import subprocess
from bs4 import BeautifulSoup
from PyPDF2 import PdfReader
from openai import OpenAI


RESULTS_DIR = "../raw_output3"
SMT_DIR = "../smt_output"
STANFORD_CS_CORE_WEBLINK = "https://www.cs.stanford.edu/bs-core-requirements"
STANFORD_SENIOR_PROJECT_WEBLINK = "https://www.cs.stanford.edu/bs-requirements-senior-project"
STANFORD_SOE_SCIENCE_WEBLINK = "https://ughb.stanford.edu/courses/approved-courses/science-courses-2023-24"
STANFORD_SEMINAR_WEBLINK = "https://exploreintrosems.stanford.edu/seminars-school-engineering"


def gpt3_infer(prompt):
	client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))
	chat_completion = client.chat.completions.create(
			messages=[
					{
					"role": "user",
					"content": f"{prompt}",
					}
			],
			model="gpt-3.5-turbo",
	)
	return chat_completion.choices[0].message.content

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

def automated_code_fixer(inferred_formulas_file, iterations):
        for i in range(iterations):
                cmd = ["python", inferred_formulas_file]
                process = subprocess.Popen(cmd, 
                           stdout=subprocess.PIPE, 
                           stderr=subprocess.PIPE)

                # wait for the process to terminate
                out, err = process.communicate()
                print(f"out:\n {out}")
                print(f"err:\n {err}")
                errcode = process.returncode
                if "Error" in err.decode("utf-8"):
                        code = open(inferred_formulas_file, "r")
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
                        reformatted_fixed_code = fixed_code.split(start)[1].split(end)[0]
                        print(fixed_code)
                        fixed_file = open(f"{inferred_formulas_file}", "w+")
                        fixed_file.write(reformatted_fixed_code)
                        fixed_file.close()
                else:
                        break
        return True
                        
                        
                
                
def extract_requirements(requirement_path):
        text = pdf_to_text(requirement_path)
        seminar_courses = weblink_to_text(STANFORD_SEMINAR_WEBLINK)
        name = os.path.basename(requirement_path)
        requirement_name, _ = name.split(".")

        requirement_prompt = f"""
        Please extract a list of requirements from the following course requirement document: 
        {text}. Please do not ignore advisor approval or deviation contraints. Please output a list of {requirement}
        from {text}. 
        """
        requirement_out = gpt3_infer(requirement_prompt)
        file = open(f"./{requirement_name}.txt", "w+")
        file.write( requirement_out)
        print(requirement_out)
        file = open(f"./{requirement}", "w+")

def read_constraints(requirement_path):
        constraints = []
        name = os.path.basename(requirement_path)
        requirement_name, _ = name.split(".")
        file = open(f"./{requirement_name}.txt", "r")
        raw_file = file.read()
        for line in raw_file.split("\n"):
                if "-" in line:
                        print(line)
                        constraints.append(line)
                        print("===========================")
        return constraints
   
        
def get_requirement(doc, requirement):
        if not os.path.exists(RESULTS_DIR):
                os.makedirs(RESULTS_DIR)
        text = pdf_to_text(doc)
        requirement =f"""
        Please extract relevant {requirement} from {text} and consult NOTES for relevant
        requiirements too if there is a NOTES section. Please output extracted requirement of {requirement} and NOTES in the document only.
        """
        individual_requirement = gpt3_infer(requirement)
        print(individual_requirement)
        return  individual_requirement
        
def translate_to_smt(dir, requirement_path, requirement): 
        if not os.path.exists(dir):
                os.makedirs(dir)
        name = os.path.basename(requirement_path)
        requirement_name, _ = name.split(".")
        requirement_out = get_requirement(requirement_path, requirement)
        formula_prompt =f"""
        Your task is to generate cvc5 smt solver formulas for the constraints in each requirement {requirement_out} you have identified.
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
                {{"Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}},
                {{"Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}}, 
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
        "Cumulative_GPA": {{
                "Undergrad": Real,
                "Graduate": Real,
        }},
        }}
        ```
        Given a transcript schema as input variables, please generate cvc5 smt solver formulas for each constraint in the 
        {requirement_out}. Below is an example formula for a given requiremet: Students must take one of the courses in (CS 100, CS 101, CS 102)
        and one of the courses in (CS 101, CS 102, CS 103). The same course cannot be used to satisfy two different requirements.
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
		```smt
		(set-logic ALL)

		(declare-const course1 String)
		(declare-const course2 String)
		assert(and (and (and (and (= course1 course) for course in Transcript.get("Courses_Taken")(= course1 course) for course in Transcript.get("Courses_Taken"))(or(= course1 "CS 100")(= course1 "CS 101")(= course1 "CS 102"))(or(= course2 "CS 101")(= course2 "CS 102")(= course2 "CS 103")) (not (= course1 course2)))))
		(check-sat)
		```
		Your task is to generate a parameterized formula reflecting the correct logic of {requirement_out}.
		"""
        formula_out = gpt3_infer(formula_prompt)
        output_filename = requirement.replace(" ", "_")
        file = open(f"{dir}/{output_filename.lower()}_formulas", "w+")
        file.write("=======================prompt===========================\n")
        file.write(formula_prompt)
        file.write("=======================formula ouput===========================\n")
        file.write(formula_out)
        prior_output = open(f"{dir}/{output_filename.lower()}_formulas", "r")
        return requirement_out, formula_out

def ms_to_smt(requirement_path):
        reqs = ["ELECTIVES", "BREADTH REQUIREMENT", "ARTIFICIAL INTELLEGIENCE DEPTH", "FOUNDATIONS REQUIERMENT",\
                "SIGNIFICANT IMPLEMENTATION REQUIREMENT", "ADDITIONAL REQUIREMENT"]
        req_out = []
        formulas = []
        for req in reqs:
                requirement_out, formula_out = translate_to_smt(SMT_DIR, requirement_path, req)
                req_out.append(requirement_out)
                formulas.append(formula_out)
        return reqs, req_out, formulas

def translate_requirements_to_formal_statements(requirement_path, requirement): 
        name = os.path.basename(requirement_path)
        requirement_name, _ = name.split(".")
        requirement_out = get_requirement(requirement_path, requirement)
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
                {{"Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}},
                {{"Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}}, 
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
        "Cumulative_GPA": {{
                "Undergrad": Real,
                "Graduate": Real,
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
        solver formulas for advisor approval, deviation constraints if there is one. Please note that your formulas should check taken courses in the transcript against each contraint and requirement. Please generate
        parameterized formulas with respect to the requirements only. 
        """
        formula_out = gpt3_infer(formula_prompt)
        output_filename = requirement.replace(" ", "_")
        file = open(f"{RESULTS_DIR}/{output_filename.lower()}_formulas", "w+")
        file.write("=======================prompt===========================\n")
        file.write(formula_prompt)
        file.write("=======================formula ouput===========================\n")
        file.write(formula_out)
        prior_output = open(f"{RESULTS_DIR}/{output_filename.lower()}_formulas", "r")
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
        python_file = open(f"{output_filename.lower()}_formulas.py", "w+")
        start = "```python"
        start2 = "```"
        end = "```"
        if start in formula_compile: 
                reformatted_formula_compile = formula_compile.split(start)[1].split(end)[0]
        if start2 in formula_compile: 
                reformatted_formula_compile = formula_compile.split(start2)[1].split(end)[0]
        else: 
                reformatted_formula_compile = formula_compile
        print(reformatted_formula_compile)
        python_file.write(reformatted_formula_compile)
        python_file_name = f"{output_filename.lower()}_formulas.py"
        return python_file_name

def auto_formulas_gen(field):
        requirement_path = f"../program_sheets/CS_{field}_2324PS.pdf"
        reqs = ["Mathematics and Science", "Technology in Society", \
                "Engineering Fundamentals", f"{field} Track Core, Depth and Senior Project"]
        final_dir = f"backend_{field}_formulas"
        if not os.path.exists(final_dir):
                os.makedirs(final_dir)
        for req in reqs:
                print(f"fixing {req}...\n")
                python_file_name = translate_requirements_to_formal_statements(requirement_path, req)
                return_value = automated_code_fixer(python_file_name, 30)
                if return_value == True: 
                        print("code fix is completed\n") 
                cmd = ["mv", python_file_name, final_dir]
                process = subprocess.Popen(cmd, 
                                stdout=subprocess.PIPE, 
                                stderr=subprocess.PIPE)

                # wait for the process to terminate
                out, err = process.communicate()
                print(f"moving formula file out:\n {out}")
                print(f"moving formula file err:\n {err}")
        
def backend_auto_formulas_gen(field):
        requirement_path = f"./program_sheets/CS_{field}_2324PS.pdf"
        reqs = ["Mathematics and Science", "Technology in Society", \
                "Engineering Fundamentals", f"{field} Track Core, Depth and Senior Project"]
        final_dir = f"./formulas/fixed_{field}_formulas"
        if not os.path.exists(final_dir):
                os.makedirs(final_dir)
        for req in reqs:
                print(f"fixing {req}...\n")
                python_file_name = translate_requirements_to_formal_statements(requirement_path, req)
                return_value = automated_code_fixer(python_file_name, 30)
                if return_value == True: 
                        print("code fix is completed\n") 
                cmd = ["mv", python_file_name, final_dir]
                process = subprocess.Popen(cmd, 
                                stdout=subprocess.PIPE, 
                                stderr=subprocess.PIPE)

                # wait for the process to terminate
                out, err = process.communicate()
                print(f"moving formula file out:\n {out}")
                print(f"moving formula file err:\n {err}")  

def main():
        sheets = ["Theory", "Info", "CompBio", "CompEng", "Indiv",\
                "Unspec", "VisComp"]
        for sheet in sheets: 
                auto_formulas_gen(sheet)
        '''
        requirement_path = "../program_sheets/Stanford_AI_MS.pdf"
        reqs = ["ELECTIVES", "BREADTH REQUIREMENT", "ARTIFICIAL INTELLEGIENCE DEPTH", "FOUNDATIONS REQUIERMENT",\
                "SIGNIFICANT IMPLEMENTATION REQUIREMENT", "ADDITIONAL REQUIREMENT"]
        
        for req in reqs:
                print(f"fixing {req}...\n")
                python_file_name = translate_requirements_to_formal_statements(requirement_path, req)
                return_value = automated_code_fixer(python_file_name, 30)
                if return_value == True: 
                        print("code fix is completed\n")
                requirement_path = "../program_sheets/Stanford_AI_MS.pdf"
        requirement_path = "../program_sheets/CS_Systems_2324PS.pdf"
        reqs = ["Mathematics and Science", "Technology in Society", \
                "Engineering Fundamentals", "Systems Track Core, Depth and Senior Project"]
        
        for req in reqs:
                print(f"fixing {req}...\n")
                python_file_name = translate_requirements_to_formal_statements(requirement_path, req)
                return_value = automated_code_fixer(python_file_name, 30)
                if return_value == True: 
                        print("code fix is completed\n")
      
        python_file_name = translate_requirements_to_formal_statements(requirement_path, req)
        return_value = automated_code_fixer(python_file_name, 30)
        if return_value == True: 
                print("code fix is completed\n")
        for req in reqs:
                python_file_name = translate_to_smt(SMT_DIR, requirement_path, req)
        '''

if __name__ == "__main__":
        main()
         
        
        

