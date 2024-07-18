import os 
import sys 
sys.path.append('/home/sallyjunsongwang/courseSAT')
from prompts.translate import (
        pdf_to_text,
        gpt_infer
)


transcript_path = "/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf"
requirement_path = "../program_sheets/Stanford_AI_MS.pdf"
requirement = pdf_to_text(requirement_path)
transcript = pdf_to_text(transcript_path)

transcript_sentence_1 = f"""
The student's name is Alice Smith, and her student ID is 123456, and 
Alice is not a coterminal student."""

transcript_sentence_2 = f"""
Alice has taken the following courses:
   - Course number CS103 titled "Logic, Automata", which is worth 3 units, and she received a grade of A.
   - Course number CS161 titled "Algorithmic Analysis", which is worth 4 units, and she received a grade of B+.
Alice has completed CS103 and CS161. These courses are counted towards her Master's degree (MS) and there are no waivers associated with these courses.
"""
requirement_sentence_1 = f"""
There is a general constraint for the MSCS Degree: The total number of units must be greater than or equal to 45.
"""

requirement_sentence_2 = f"""
 To fulill MSCS Degree and foundations requirements, students need to satisfy each sub requirement of foundations requirements from this document: {requirement}.
"""

def find_IR(requirement_path, transcript_path):
        prompt = f"""
        Please fill out a json schema template containing Student (student information from the transcript),
        Courses_Taken (a list of taken courses with relevant course information from the transcript), 
        Approval (whether an advior has approved a taken course for degree requirements. This is typically unknown from the transcript unless
        otherwise specified), and Cumulative GPA (cumulative GPA for undnergraduate and graduate degrees) 
        from a given transcript. Here is the
        transcript: {transcript}. Please output a filled transcript json schema only. 
        ```json
        transcript = {{
        "Student": {{
                "Name": String,
                "StudentID": Integer,
                "Coterm": Boolean
        }},
        "Courses_Taken": [
                {{"Course_ID": Integer, "Title": String, "Earned_Units": Integer, "Grade": String}},
                {{"Course_ID": "", "Title": "", "Units": , "Grade": }}, 
                ...
        ]
        "Approval": {{
                "Approved": Boolean,
                "Approved_By": String,
                "Course_ID": String
        }},
        
        "Cumulative_GPA": {{
                "Undergrad": Real,
                "Graduate": Real,
        }},
        }}
        ```
        """
        out = gpt_infer(prompt)
        print(out)
        print("=======================================\n")     


def failed_baseline():
        prompt = f""" Your task is to consturct an abstract syntax tree that caputure constraints and relationships 
        in the following information: {transcript_sentence_1}, {transcript_sentence_2}, {requirement_sentence_1}, {requirement_sentence_2}.
        """
        out = gpt_infer(prompt)
        print(out)
        file = open("./llm_ast.txt", "w+")
        file.write(out)
        print("=======================================\n")


def failed_baseline_2():
        prompt = f"""A student has taken CS 101, write a smt program to test if he saitsfy the reqirement of taking 
        courses above 100.. 
        """
        out = gpt_infer(prompt)
        print(out)
        file = open("./llm_formula2.txt", "w+")
        file.write(out)
        print("=======================================\n")       
         
find_IR(requirement_path, transcript_path)
#failed_baseline_2()


	if requirement == "ELECTIVES":
		extract_prompt = f"""
		Please extract the seminar course numbers from {seminar_courses} based on the following: {text}.
		Please pay attention to notes for relevant electives of {requirement} and extract relevant elective courses related to {requirement} too.
		Remember, please output output all course numbers in a single python list [] only.  
		"""

		seminar_courses = gpt_infer(extract_prompt)
		print(seminar_courses)
		course_file = open(f"{RESULTS_DIR}/{requirement}_course_list.txt", "w+")
		course_file.write(seminar_courses)

		solver_prompt = f"""
		Given a list of courses {seminar_courses}, please translate each course into 
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

		formula_prompt = f"""
		Your task is to generate python compilable CVC5 solver formulas based on constraints in a course requirements document. 
		Given a list of related elective courses {seminar_courses} from {requirement} in the following
		document: {text}, please carefully analyze the units and course requirements in the {requirement} and generate solver formulas in python code
		that check if specified constraints are satisfied accordingly. You can assume a user input of elective courses in a variable `elective_choices` in the following format: 
		Please make sure the genrated constraints also satisfy specified seminar course requirements {seminar_courses}.
  		Remember, you must generate cvc5 formulas in python code that meet 
		specified constraints of {requirement} in {text}.
		"""
		formula_statements = gpt_infer(formula_prompt)
		print(formula_statements)
		formula_file = open(f"{RESULTS_DIR}/{requirement}_solver_formulas.py", "w+")
		formula_file.write(formula_statements)