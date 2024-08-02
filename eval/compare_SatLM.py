import os 
import sys 
import jsonlines
from openai import OpenAI
from PyPDF2 import PdfReader


RESULTS_DIR = "./SatLM_Baseline"
EVAL_DATA = "./eval/data"
requirement_path = "../program_sheets/Stanford_AI_MS.pdf"



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


def pdf_to_text(doc):
	reader = PdfReader(doc)
	number_of_pages = len(reader.pages)
	text = ""
	for i in range(0, number_of_pages):
		page = reader.pages[i]
		text += page.extract_text()
	return text

def get_datasets(dataFolder):
	for filename in os.listdir(dataFolder):
         	f = os.path.join(dataFolder, filename)
		data = json.load(f)
        
        

def compare_satLM():
        requirement = pdf_to_text(requirement_path)
        prompt = f"""
        Your task is to generate z3py formulas given consrtraints in a requrement document.
        Here is an example translation for the text "Dorothy took her daughter Michelle and her mother Gabrielle car shopping.
                Q: How is [Michelle] related to [Gabrielle]?"
                
                # [Dorothy] took her daughter [Michelle] and her mother [Gabrielle] car shopping.
                relation(Dorothy, Michelle) = (mother, daughter)
                relation(Dorothy, Gabrielle) = (daughter, mother)
                # How is [Michelle] related to [Gabrielle]?
                solve(relation(Michelle, Gabrielle)). Please translate this requirement document: {requirement}
                into z3py formulas."""
        out = gpt3_infer(prompt)
        print(out)
        file = open(f"{RESULTS_DIR}/satLM.txt", "w+")
        file.write(out)
        file.close()

compare_satLM()
