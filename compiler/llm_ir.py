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
        prompt = f""" Your task is to fill in the blanks such as "" and Bool in a json file with given
        sentences and texts. The sentence will be given to you one by one. You should output a filled json file
        from information in the given sentences and texts. 
        Given {transcript_sentence_1} and {transcript_sentence_2}, please fill in the following json file 
        ```json
                intermediate_representation = {{
        "Student": {{
                "Name": "",
                "StudentID": "",
                "Coterm": Bool
        }},
        "Courses": [
                {{"CourseNumber": "", "Title": "", "Units": , "Grade": ""}},
                {{"CourseNumber": "", "Title": "", "Units": , "Grade": ""}}
        ],
        "Requirements": [
                {{
                "RequirementType": "",
                "Satisfied": Bool,
                "SubRequirements": [
                        {{"Course": "", "Satisfied": Bool, "WaiverAllowed": }},
                        {{"Course": "", "Satisfied": Bool, "WaiverAllowed": }},
                        {{"Course": "", "Satisfied": Bool, "WaiverAllowed": }},
                        {{"Course": "", "Satisfied": Bool, "WaiverAllowed": }},
                        {{"Course": "", "Satisfied": Bool, "WaiverAllowed": }},
                ]
                }}
        ],
        "Relations": [
                {{"RelationType": "", "Attributes": {{"Completed": , "ForMS": , "Waivers": []}}}}
        ],
        "Constraints": [
                {{"ConstraintType": "", "Condition": ""}}
        ]
        }}
        ```
        Please remember your json output from prior step. Now given {requirement_sentence_1} and 
        {requirement_sentence_2}, please fill in all remaining blanks in the json file and output the filled json file only. 
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
         
#find_IR(requirement_path, transcript_path)
failed_baseline()
