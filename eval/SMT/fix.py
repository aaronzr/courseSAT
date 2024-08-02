import os 
import sys 
import itertools
import subprocess
from openai import OpenAI

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
                        fixed_file = open(f"{inferred_formulas_file}", "w+")
                        fixed_file.write(fixed_code)
                        fixed_file.close()
                else:
                        break
        return True

'''
test_path = "./"
for subdir, dirs, files in os.walk(test_path):
        for file in files:
                if ".py" in file: 
                        codeFixer(file, 30)
codeFixer("0.py", 30)
codeFixer("1.py", 30)
codeFixer("2.py", 30)
'''
codeFixer("6.py", 30)