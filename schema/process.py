import os 
import sys 
import json
import requests
from bs4 import BeautifulSoup
from PyPDF2 import PdfReader
from openai import OpenAI

RESULTS_DIR = "../schema_results"

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
        """
        schema = gpt_infer(prompt)
        print(schema)
        print("=======================================\n") 
        if not os.path.exists(results_dir):
                os.makedirs(results_dir)
        file = open(f"{results_dir}/{transcript_name}.json", "w+")
        file.write(schema)  

def parse_schema(schema_path):
        with open(schema_path, 'r') as file:
                data = json.load(file)
        name = os.path.basename(schema_path)
        transcript_name, _ = name.split(".")
        student = data.get("Student", {})
        ap_credits = data.get("AP_Credits", [])
        courses_taken = data.get("Courses_Taken", [])
        approval = data.get("Approval", [])
        deviations = data.get("Deviations", [])
        cumulative_gpa = data.get("Cumulative_GPA", {})

        # Accessing student information
        student_name = student.get("Name")
        student_program = student.get("Program")
        student_id = student.get("StudentID")
        student_coterm = student.get("Coterm")

        print(f"Student Name: {student_name}, Program: {student_program}, ID: {student_id}, Coterm: {student_coterm}")

        # Accessing AP Credits
        for credit in ap_credits:
                advanced_placement = credit.get("Advanced_Placement")
                earned_units = credit.get("Earned_Units")
                print(f"AP Credit: {advanced_placement}, Earned Units: {earned_units}")

        # Accessing Courses Taken
        for course in courses_taken:
                course_id = course.get("Course_ID")
                title = course.get("Title")
                earned_units = course.get("Earned_Units")
                grade = course.get("Grade")
                print(f"Course ID: {course_id}, Title: {title}, Earned Units: {earned_units}, Grade: {grade}")

        # Accessing Approval Information
        for app in approval:
                approved = app.get("Approved")
                approved_by = app.get("Approved_By")
                approved_course_id = app.get("Approved_Course_ID")
                print(f"Approved: {approved}, Approved By: {approved_by}, Approved Course ID: {approved_course_id}")

        # Accessing Approval Information
        for dev in deviations:
                approved_by = app.get("Approved_By")
                dev_ourse_id = app.get("Deviated_Course_ID")
                print(f"deviations: {dev}, Approved By: {approved_by}, Deviated Course ID: {dev_ourse_id}")
        # Accessing Cumulative GPA
        undergrad_gpa = cumulative_gpa.get("Undergrad")
        graduate_gpa = cumulative_gpa.get("Graduate")

        print(f"Undergrad GPA: {undergrad_gpa}, Graduate GPA: {graduate_gpa}")
        return student, ap_credits, courses_taken, approval, cumulative_gpa
        
        
transcript_path = "/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf"
requirement_path = "../program_sheets/Stanford_AI_MS.pdf"
schema_path = "../schema_results/stanford_transcript1.json"
#process_individual_transcript(RESULTS_DIR, transcript_path)
parse_schema(schema_path)
