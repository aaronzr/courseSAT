import os
import pygsheets
import subprocess
import pandas as pd
import numpy as np
from openai import OpenAI

#authorization
gc = pygsheets.authorize(service_file='credentials.json')
sh = gc.open('working_constraints_worksheet')
dir = "worksheet"
#select the first sheet 
ORIGINAL_SHEET = sh[7]

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
                

def pythonicFormula_prompt_per_worksheet(worksheet):
        constraint = ""
        for index, row in worksheet.iterrows():
                if row["Type"] == "Worksheet" and row["Form Name"] != None:
                        background = f"""Your task is to generate cvc5 python solver formulas for \
                        {row["Form Name"]} requirements. You will be given a set of constraints related to 
                        {row["Form Name"]} and you should generate cvc5 python solver formulas reflecting the correct logic of each given constraint."""
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
                        Here is a template for you to follow:
                        ```
                        #helper function for solver initialization
                        def solver_init(): 
                                solver = cvc5.Solver()
                                solver.setOption("produce-unsat-cores", "true")
                                solver.setOption("produce-models", "true")
                                solver.setLogic("ALL")
                                return solver 
                                
                        #helper function for solver initialization
                        def result_checker(solver, variables):
                                result = solver.checkSat()
                                trace = ""
                                print("Satisfiability:", result)
                                if result.isSat():
                                        print("SAT")
                                        if variables: 
                                                for variable in variables: 
                                                        trace = solver.getValue(variable)
                                                        print(f"Model for {{variable}}:", trace)
                                else: 
                                        trace = solver.getUnsatCore()
                                        print("Unsat requirement core is: ", trace)
                                return result, trace
                        
                        #function for checking requirements given a path to a transcript schema
                        def check_requirements(transcript_path):
                                solver = solver_init()
                                with open(transcript_path, 'r') as file:
                                        transcript = json.load(file)
                                #generated formulas below:
                                ...
                        
                        #supply a transcript schema to check whether requirements are satisfied 
                        given smt python formulas    
                        if __name__ == "__main__":
	                        schema_path = "../schema_results/stanford_transcript1.json"
                                check_requirements(schema_path)
                        ```
                        Remember, it's very important that you generate smt formulas that PARAMETRIZE
                        course variables to check variables in a given transcript against requirements. Please only generate 
                        parameterized formulas and use the format as above.
                        """
                if row["Kind"] == "input" and row["Type"] == "Enum" and row["Name"] != None and row["Description"] != None:
                        if row["Input Condition"] == None: 
                                constraint += f"""The {row["Name"]} checks whether a student has taken a course in {row["Enum Values"]}. \
                                Your task is to follow the template and generate parameterized smt python solver formula reflecting the correct logic of this constraint: {constraint}"""
                        else:
                                constraint += f"""The {row["Name"]} checks whether a student has taken a course in {row["Enum Values"]} and please carefully study
                                {row["Input Condition"]} that applies to {row["Enum Values"]}.  \
                                Your task is to follow the template and generate parameterized smt python solver formula reflecting the correct logic of this constraint: {constraint} and {row["Input Condition"]}"""
                                
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
                        
def translate_to_formulas(worksheet, name):
        prompt = pythonicFormula_prompt_per_worksheet(worksheet) 	
        formulas = gpt4_infer(prompt)
        file = open(f"{name}_formula.py", "w+")
        file.write(formulas)
        automated_code_fixer(f"{name}_formula.py", 30)
        print(formulas)

       
        
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
math_science_sheet = df.apply(lambda x: x[7:12])
electives = df.apply(lambda x: x[13:16])
print(math_science_sheet)
translate_to_formulas(math_science_sheet, "(math_science_sheet")
print(electives)
translate_to_formulas(electives, "electives")
#update the first sheet withdf, starting at cell B2. 
#wks.set_dataframe(df,(1,1))
translate_to_smt(math_science_sheet)
translate_to_smt(electives)