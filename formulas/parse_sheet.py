import os
import pygsheets
import pandas as pd
from openai import OpenAI

#authorization
gc = pygsheets.authorize(service_file='credentials.json')
sh = gc.open('working_constraints_worksheet')
dir = "worksheet"

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

#select the first sheet 
wks = sh[6]
df = wks.get_as_df()
print(df.loc[8]['Form Name'])
#update the first sheet with df, starting at cell B2. 
#wks.set_dataframe(df,(1,1))

def translate_to_smt(): 
        formula_prompt =f"""
        Your task is to generate cvc5 smt solver formulas for a list of required courses: {df.loc[9:17]['Name'].to_string(index=False)} and 
        related constraints {df.loc[105]['Name']}.
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
		Your task is to generate a parameterized formula reflecting the correct logic of a list of required courses: {df.loc[9:17]['Name'].to_string(index=False)} and 
        related constraints {df.loc[105]['Name']}..
		"""
        formula_out = gpt4_infer(formula_prompt)
        output_filename = df.loc[8]['Form Name'].replace(" ", "_")
        file = open(f"{dir}/{output_filename.lower()}_formulas", "w+")
        file.write("=======================prompt===========================\n")
        file.write(formula_prompt)
        file.write("=======================formula ouput===========================\n")
        file.write(formula_out)
        print(formula_out)

translate_to_smt()