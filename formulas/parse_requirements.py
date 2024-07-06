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
STANFORD_SEMINAR_WEBLINK = "https://exploreintrosems.stanford.edu/seminars-school-engineering"

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

def extract_requirements(requirement_path):
        text = pdf_to_text(requirement_path)
        seminar_courses = weblink_to_text(STANFORD_SEMINAR_WEBLINK)
        name = os.path.basename(requirement_path)
        requirement_name, _ = name.split(".")

        requirement_prompt = f"""
        Please extract a list of requirements from the following course requirement document: 
        {text}. Please output a list of requirements. 
        """
        requirement_out = gpt_infer(requirement_prompt)
        file = open(f"./{requirement_name}.txt", "w+")
        file.write( requirement_out)
        print(requirement_out)

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
   
        
 
        

def translate_requirements_to_formal_statements(requirement_path): 
        name = os.path.basename(requirement_path)
        requirement_name, _ = name.split(".")
        file = open(f"./{requirement_name}.txt", "r")   
        requirement_out = file.read()  
        formula_prompt =f"""
        Your task is to generate cvc5 python solver formulas for the constraints in each requirement {requirement_out} you have identified.
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
        "Approval": [
                {{
                "Approved": Boolean or "UNKOWN",
                "Approved_By": String or None,
                "Approved_Course_ID": String or None
        }},
          {{
                "Approved": Boolean or "UNKNOWN",
                "Approved_By": String or None when "Approved"=="UNKNOWN",
                "Approved_Course_ID": String or None when "Approved"=="UNKNOWN"
        }},
        ]
        
        "Cumulative_GPA": {{
                "Undergrad": Real,
                "Graduate": Real,
        }},
        }}
        ```
        Given a transcript schema as input variables, please generate cvc5 smt solver formulas for each constraint in the 
        {requirement_out}. Below is an example formula for a given requiremet: Pick one of the courses (100, 101, 102)
        and one of the courses (101, 102, 103). The same course cannot be used to satisfy two different requirements.
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
        When generating cvc5 solver formulas, please use the variables in the transcript schema as declared. Please generate
        formulas with respect to the requirements only. 
        """
        formula_out = gpt_infer(formula_prompt)
        file = open(f"{RESULTS_DIR}/zero_shot_formulas", "w+")
        file.write("=======================prompt===========================\n")
        file.write(formula_prompt)
        file.write("=======================formula ouput===========================\n")
        file.write(formula_out)
        print(formula_out)
        
requirement_path = "../program_sheets/Stanford_AI_MS.pdf"
#extract_requirements(requirement_path)
#read_constraints(requirement_path)
translate_requirements_to_formal_statements(requirement_path)
 