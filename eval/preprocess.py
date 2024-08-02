import os 
import sys 
import itertools
import subprocess
import pandas as pd
from utils import *
from openai import OpenAI

LSAT_PROMPT = """
Generate python code for the given file. Below are two examples first: 
```
x = Variable() # declare a variable
People = [Alice, Bob] # declare enum set
Cities = [Austin, Boston] # declare enum set
Food = [Apple, Banana] # declare enum set
visit = Function(People, Cities) # declare function
eats = Function(People, Food) # declare function
visit(Alice) != visit(Bob) # logic
ForAll(x: People, Implies(visit(x) == Austin, eats(x) == Banana))
```
And anothe example for LSAT:
```
Nine different treatments are available for a certain illness: three antibiotics—F, G, and H—three dietary
regimens—M, N, and O—and three physical therapies—U, V, and W. For each case of the illness, a doctor
will prescribe exactly five of the treatments, in accordance with the following conditions: If two of the
antibiotics are prescribed, the remaining antibiotic cannot be prescribed. There must be exactly one dietary
regimen prescribed. If O is not prescribed, F cannot be prescribed. If W is prescribed, F cannot be prescribed.
G cannot be prescribed if both N and U are prescribed. V cannot be prescribed unless both H and M are
prescribed.
Question: If O is prescribed for a given case, which one of the following is a pair of treatments both of which
must also be prescribed for that case?
(A) F, M (B) G, V (C) N, U (D) U, V (E) U, W
treatments = [F, G, H, M, N, O, U, V, W]
antibiotics = [F, G, H]
dietary_regimens = [M, N, O]
physical_therapies = [U, V, W]
prescribed = Function(treatments, bool)
Count([t:treatments], prescribed(t)) == 5
Count([a:antibiotics], prescribed(a)) <= 2
Count([d:dietary_regimens], prescribed(d)) == 1
Implies(Not(prescribed(O)), Not(prescribed(F)))
Implies(prescribed(W), Not(prescribed(F)))
Implies(And(prescribed(N), prescribed(U)), Not(prescribed(G)))
Implies(prescribed(V), And(prescribed(H), prescribed(M)))
solve(Implies(prescribed(O), And(prescribed(U), prescribed(V)))) # (A)
solve(Implies(prescribed(O), And(prescribed(G), prescribed(V)))) # (B)
solve(Implies(prescribed(O), And(prescribed(N), prescribed(U)))) # (C)
solve(Implies(prescribed(O), And(prescribed(U), prescribed(V)))) # (D)
solve(Implies(prescribed(O), And(prescribed(U), prescribed(W)))) # (E)
```
Here is the file you should generate z3py formulas: 
"""

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

def read_manual_prompt(task, prompt_id, style_template):    
    prompt_lines = read_jsonline(f'/home/sallyjunsongwang/courseSAT/SAT-LM/manual_prompts/{task}.jsonline')
    d = dict([(x["id"], x) for x in prompt_lines])
    selected = d[prompt_id]
    assert selected["style_template"] == style_template
    print(selected["prompt"])
    return selected["prompt"]

def get_datasets(dataFolder):
        counter = 0
        context_df = [] 
        question_df = []
        label_df = []
        name_df = []
        for filename in os.listdir(dataFolder):
                print(f"===============counter {counter}====================\n")
                counter += 1
                if "json" and "proof" in filename: 
                        name, _ = filename.split(".")
                        f = os.path.join(dataFolder, filename)
                        with open(f) as file:
                                prompts = read_jsonline(f)
                                for prompt in prompts: 
                                        print(prompt)
                                        for i in range(len(prompt)):
                                                print(prompt[i]['id'])
                                                print(prompt[i]['context'])
                                                print(prompt[i]['question'])
                                                print(prompt[i]['label'])
                                                context_df.append(prompt[i]['context'])
                                                question_df.append(prompt[i]['question'])
                                                label_df.append(prompt[i]['label'])
                                                smtDataEval([prompt[i]['context']], [prompt[i]['question']], [prompt[i]['label']], ["proof"+prompt[i]['id']])

                if "json" and "clutrr" in filename: 
                        name, _ = filename.split(".")
                        f = os.path.join(dataFolder, filename)
                        with open(f) as file:
                                prompts = read_jsonline(f)
                                for prompt in prompts: 
                                        print(prompt)
                                        for i in range(len(prompt)):
                                                print(prompt[i]['id'])
                                                print(prompt[i]['query'])
                                                print(prompt[i]['label'])
                                                context_df.append([""])
                                                question_df.append(prompt[i]['query'])
                                                label_df.append(prompt[i]['label'])
                                                smtDataEval([prompt[i]['query']], [prompt[i]['query']], [prompt[i]['label']], ["clutrr"+prompt[i]['id']])
                if "json" and "gsm" in filename: 
                        name, _ = filename.split(".")
                        f = os.path.join(dataFolder, filename)
                        with open(f) as file:
                                prompts = read_jsonline(f)
                                for prompt in prompts: 
                                        print(prompt)
                                        for i in range(len(prompt)):
                                                print(prompt[i]['id'])
                                                print(prompt[i]['question'])
                                                print(prompt[i]['label'])
                                                context_df.append([""])
                                                question_df.append(prompt[i]['question'])
                                                label_df.append(prompt[i]['label'])
                                                satLMDataEval(context_df, question_df, label_df, name_df)
                                                smtDataEval([prompt[i]['question']], [prompt[i]['question']], [prompt[i]['label']], ["gsm"+prompt[i]['id']])
                if "json" and "boardmain" in filename: 
                        name, _ = filename.split(".")
                        f = os.path.join(dataFolder, filename)
                        with open(f) as file:
                                prompts = read_jsonline(f)
                                for prompt in prompts: 
                                        print(prompt)
                                        for i in range(len(prompt)):
                                                print(prompt[i]['id'])
                                                print(prompt[i]['question'])
                                                print(prompt[i]['label'])
                                                context_df.append([""])
                                                question_df.append(prompt[i]['question'])
                                                label_df.append(prompt[i]['label'])
                                                smtDataEval([prompt[i]['question']], [prompt[i]['question']], [prompt[i]['label']], ["boardmain"+prompt[i]['id']])
                if "json" and "arlsat" in filename:                    
                        name, _ = filename.split(".")
                        f = os.path.join(dataFolder, filename)
                        with open(f) as file:
                                prompts = read_jsonline(f)
                                for prompt in prompts: 
                                        print(prompt)
                                        for i in range(len(prompt)):
                                                print(prompt[i]['id'])
                                                print(prompt[i]['question'])
                                                print(prompt[i]['choices'])
                                                context_df.append([""])
                                                question_df.append(prompt[i]['question'])
                                                label_df.append(prompt[i]['choices'])
                                                smtDataEval([prompt[i]['question']], [prompt[i]['choices']], [prompt[i]['label']], ["arlsat"+prompt[i]['id']])
        return context_df, question_df, label_df, name_df
                

def extractLsat():
        count = 0
        dataFolder = "/home/sallyjunsongwang/courseSAT/SAT-LM/annotations/arlsat"
        for subdir, dirs, files in os.walk(dataFolder):
                for file in files:
                        count += 1
                        print("=================\n")
                        file_path = os.path.join(subdir, file)
                        print(file_path)
                        print(count)
                        if "satlm" in file_path:
                                f = open(file_path, "r")
                                fixed_code = f.read()
                                start = "\"\"\""
                                end = "\"\"\""
                                reformatted_fixed_code = fixed_code.split(start)[1].split(end)[0]
                                file = open(f"lsat/{count}.py", "w+")   
                                file.write(reformatted_fixed_code)
                                file.close()   
                                
                                    
def codeFixer(inferred_formulas_file, iterations):
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
                     
                                
def read_context(context_list): 
        statament = ""
        for i in range(len(context_list)): 
                statement += context_list[i]
        return statament
                
def smtDataEval(context_df, question_df, label_df, name_df):
        for i in range(len(context_df)): 
                prompt = f"""
                You are an amazing parser that translates natural language into CVC5 SMT python formulas. 
                You will be given a list of conetxtual statements first and then a test or question statement for the solver to evaluate
                whether the test statement is satisfied or unsatisfied or evaluate to a possible answe to the question statement given your translated formulas. 
                Your task is to identify prarameters given the statements and generate parameterized CVC5 python formulas sentence by sentence. In the end, we
                will use cvc5 SMT solver to evaluate the test statement. Here are the conetxtual statements: 
                {context_df[i]} and a test statement: {question_df[i]}. Please translate each statement into a cvc5 python formula
                and generate a test case to ensure the logic and syntax of your code is correct. 
                Now please carefully study and translate each sentence in {context_df[i]} and {question_df[i]}.
                """
                gptOut = gpt4_infer(prompt)
                outFile = open(f"SMT/{name_df[i]}.py", "w+")
                print("\n=======================questions for prompt================================\n")
                outFile.write(f"{context_df[i]}")
                outFile.write(str(question_df[i]))
                print("\n=======================output================================\n")
                outFile.write(gptOut)
                codeFile = open(f"SMT/{name_df[i]}_code.py", "w+")
                codeFile.write(gptOut)
                codeFixer(f"SMT/{name_df[i]}_code.py", 30)
                      
def smtLSATEval(test_path):
        for subdir, dirs, files in os.walk(test_path):
                print("hello")
                for file in files:
                        file_path = os.path.join(subdir, file)
                        lsatFile = open(file_path, "r")
                        prompt = f"""
                        You are an amazing parser that translates LSAT questions into CVC5 SMT python formulas. 
                        You will be given an LSAT question with choices for the solver to evaluate
                        whether each choice is satisfied or unsatisfied given your translated formulas. Your task is to identify prarameters given the 
                        statements in the LSAT question and generate parameterized CVC5 python formulas sentence by sentence. In the end, we
                        will use cvc5 SMT solver to evaluate whether a given choice is satisfied. Please carefully study and translate each statement into a cvc5 python formula
                        and generate a test case to ensure the logic and syntax of your code is correct. 
                        Please generate cvc5 python formulas for each sentence in this LSAT question: {lsatFile.read()}
                        """
                        output = gpt4_infer(prompt)
                        outFile = open(f"SMT/{file}", "w+")
                        print("\n=======================questions for prompt================================\n")
                        outFile.write(lsatFile.read())
                        print("\n=======================output================================\n")
                        outFile.write(output)
                        codeFile = open(f"SMT/code_{file}", "w+")
                        #codeFile.write(output)
                        codeFile.close()
                        codeFixer(f"SMT/code_{file}", 30)

        
        
def satLMDataEval(context_df, question_df, label_df, name_df):
        for i in range(len(context_df)): 
                if "boardmaindp1" in name_df[i]:
                        board_prompt = read_manual_prompt("boardmaindp1", "satlm", "satlm")
                        board_output = gpt4_infer(board_prompt)
                        boardFile = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        boardFile.write("\n=====================prompt======================\n")
                        boardFile.write(board_prompt)
                        boardFile.write("\n=====================output======================\n")
                        boardFile.write(board_output)
                        
                if "boardmaindp2" in name_df[i]:
                        board_prompt2 = read_manual_prompt("boardmaindp2", "satlm", "satlm")
                        board_output2 = gpt4_infer(board_prompt2)
                        boardFile2 = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        boardFile2.write("\n=====================prompt======================\n")
                        boardFile2.write(board_prompt2)
                        boardFile2.write("\n=====================output======================\n")
                        boardFile2.write(board_output2)
                        
                if "boardmaindp3" in name_df[i]:
                        board_prompt3 = read_manual_prompt("boardmaindp3", "satlm", "satlm")
                        board_output3 = gpt4_infer(board_prompt3)
                        boardFile3 = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        boardFile3.write("\n=====================prompt======================\n")
                        boardFile3.write(board_prompt3)
                        boardFile3.write("\n=====================output======================\n")
                        boardFile3.write(board_output3)
                
                if "arlsat" in name_df[i]:
                        lsat_prompt = LSAT_PROMPT + lsatFile.read()
                        lsat_output = gpt4_infer(lsat_prompt)
                        lsat_outFile = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        lsat_outFile.write("\n=====================prompt======================\n")
                        lsat_outFile.write(lsat_prompt)
                        lsat_outFile.write("\n=====================output======================\n")
                        lsat_outFile.write(lsat_output)
                        
                if "clutrr" in name_df[i]:
                        clutrr_prompt = read_manual_prompt("clutrr", "satlm", "satlm")
                        clutrr_output = gpt4_infer(clutrr_prompt)
                        clutrr_outFile = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        clutrr_outFile.write("\n=====================prompt======================\n")
                        clutrr_outFile.write(clutrr_prompt)
                        clutrr_outFile.write("\n=====================output======================\n")
                        clutrr_outFile.write(clutrr_output)
                
                if "gsm" in name_df[i]:
                        gsm_prompt = read_manual_prompt("gsm", "satlm", "satlm")
                        gsm_output = gpt4_infer(gsm_prompt)
                        gsm_outFile = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        gsm_outFile.write("\n=====================prompt======================\n")
                        gsm_outFile.write(gsm_prompt)
                        gsm_outFile.write("\n=====================output======================\n")
                        gsm_outFile.write(gsm_output)
                
                if "proofd5" in name_df[i]:
                        proof_prompt = read_manual_prompt("proofd5", "satlm", "satlm")
                        proof_output = gpt4_infer(proof_prompt)
                        proof_outFile = open(f"satLM/satLM_{name_df[i]}.py", "w+")
                        proof_outFile.write("\n=====================prompt======================\n")
                        proof_outFile.write(proof_prompt)
                        proof_outFile.write("\n=====================output======================\n")
                        proof_outFile.write(proof_output)
                
        
def satLMLSATEval(test_path):
        for subdir, dirs, files in os.walk(test_path):
                for file in files:
                        file_path = os.path.join(subdir, file)
                        lsatFile = open(file_path, "r")
                        prompt = LSAT_PROMPT + lsatFile.read()
                        output = gpt4_infer(prompt)
                        outFile = open(f"satLM/satLM_{file}", "w+")
                        print("\n=======================questions for prompt================================\n")
                        outFile.write(lsatFile.read())
                        print("\n=======================output================================\n")
                        outFile.write(output)
        
if __name__ == "__main__":
        test_path = "./data/lsat"
        context_df, question_df, label_df, name_df = get_datasets("data")
        #smtDataEval(context_df, question_df, label_df, name_df)
        #satLMDataEval(context_df, question_df, label_df, name_df)
        smtLSATEval(test_path)
        #satLMLSATEval(test_path)
        #read_manual_prompt("boardmaindp1", "satlm", "satlm")
        #read_manual_prompt("arlsat", "cot", "cot")
        #extractLsat()