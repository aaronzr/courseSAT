import os
import pygsheets
import pandas as pd
import numpy as np
from openai import OpenAI

#authorization
gc = pygsheets.authorize(service_file='credentials.json')
sh = gc.open('working_constraints_worksheet')
dir = "worksheet"
#select the first sheet 
ORIGINAL_SHEET = sh[6]

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


def formula_prompt_per_worksheet(worksheet):
        constraint = ""
        for index, row in worksheet.iterrows():
                if row["Type"] == "Worksheet" and row["Form Name"] != None:
                        background = f"""Your task is to generate cvc5 smt solver formulas for \
                        {row["Form Name"]} requirements. You will be given a set of constraints related to 
                        {row["Form Name"]} and you should generate cvc5 smt solver formulas reflecting the correct logic of each given constraint."""
                        example = f"""
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
                        Given a transcript schema as input variables, please generate cvc5 smt solver formulas for required courses and relevant constraint. Below is an example formula for a given requiremet: Students must take one of the courses in (CS 100, CS 101, CS 102)
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
                        """
                if row["Kind"] == "input" and row["Type"] == "Enum" and row["Name"] != None and row["Description"] != None:
                        constraint += f"""The {row["Name"]} checks whether a student has taken {row["Enum Values"]}. \
                        Your task is to generate a parameterized smt solver formula reflecting the correct logic of this constraint: {constraint}"""
        prompt = background + example + constraint
        return prompt
                

def translate_to_smt(worksheet):
        prompt = formula_prompt_per_worksheet(worksheet) 	
        formulas = gpt4_infer(prompt)
        for index, row in worksheet.iterrows():
                if row["Kind"] == "output" and row["Type"] == "formulas" and row["Name"] == "SMT":
                        row["Actions"] = formulas
                        ORIGINAL_SHEET.insert_rows(index, 1, np.array(row.values.tolist()).T.tolist())
        file = open(f"output.txt", "w+")
        file.write("=======================prompt===========================\n")
        file.write(prompt)
        file.write("=======================formula ouput===========================\n")
        file.write(formulas)
        print(formulas)



df = ORIGINAL_SHEET.get_as_df()
working_spreadsheet = df.apply(lambda x: x[8:15])
print(working_spreadsheet)
#update the first sheet withdf, starting at cell B2. 
#wks.set_dataframe(df,(1,1))
translate_to_smt(working_spreadsheet)