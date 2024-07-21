import os 
import sys 
import json
import requests
import subprocess
from bs4 import BeautifulSoup
from PyPDF2 import PdfReader
from openai import OpenAI

RESULTS_DIR = "schema_results"

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

#we need to explicitly tell LLM to fill in none or unknown for Apprval fields.
#Otherwise, it will fill in false
def process_individual_transcript(results_dir, transcript_path):
        transcript = pdf_to_text(transcript_path)
        name = os.path.basename(transcript_path)
        transcript_name, _ = name.split(".")
        prompt = f"""
        Please fill out a json schema template containing Student (student information from the given transcript),
        AP_Credits (Advanced Placement title and Earned Units from the given transcript),
        Courses_Taken (a list of taken courses with relevant course information from the given transcript), 
        Deviations (a list of taken courses deviated from major or specializaion requirements, but can be approved by an advisor to meet a requirement),
        Approval (whether an advior has approved a taken course for degree requirements. This is typically false or unknown from the transcript unless
        otherwise specified), and Cumulative GPA (cumulative GPA for undnergraduate and graduate degrees) 
        from a given transcript. It's vitally IMPORTANT that you double check and fill in correct information from the given transcript.
        Here is the transcript: {transcript}. Please output a filled transcript json schema in the following format only. Your output MUST strictly follow the format.
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
                schema_fix = read_code.split(start)[1].split(end)[0]
                if "transcript = " in schema_fix: 
                        schema_fix = schema_fix.replace("transcript =","").strip()
        else:
                schema_fix = schema
        if not os.path.exists(results_dir):
                os.makedirs(results_dir)
        file = open(f"{results_dir}/{transcript_name}.json", "w+")
        file.write(schema_fix)  
        file.close()
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

if __name__ == "__main__":
        transcript_path = "/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf"
        requirement_path = "../program_sheets/Stanford_AI_MS.pdf"
        schema_path = "../schema_results/stanford_transcript1.json"
        process_individual_transcript(RESULTS_DIR, transcript_path)
        automated_code_fixer(schema_path, 10)



