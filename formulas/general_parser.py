import os
import openai
from openai import OpenAI
from parse_requirements import gpt_infer, pdf_to_text, weblink_to_text

TAX_RESULT = "../tax_rawoutput"
FORM_2848 = "https://www.irs.gov/instructions/i2848#en_US_202109_publink100013106"
FORM_2848_NAME = "f2848"
FORM_iw7 = "../Tax/iw7.pdf"
FORM_iw7_NAME = "iw7"

COMPLIANCE_RESULT = "../compliance_rawoutput"
FINRA_2090 = "https://www.finra.org/rules-guidance/rulebooks/finra-rules/2090"
FINRA_2090_NAME = "finra_2090"
FINRA_2111 = "https://www.finra.org/rules-guidance/rulebooks/finra-rules/2111"
FINRA_2111_NAME = "finra_2111"

def extract_tax_requirement(dir, link, filename):
        if not os.path.exists(dir):
                os.makedirs(dir)
        if "https://" in link: 
                text = weblink_to_text(link)
        else:
                text = pdf_to_text(link)
        constraint_prompt = f"""
        Please extract each requirement and constraint in {text}. 
        """
        constraints = gpt_infer(constraint_prompt)
        print(constraints)
        file = open(f"{dir}/{filename}", "w+")
        #file.write("===================constraint prompt===========================\n")
        #file.write(constraint_prompt)
        file.write("===================generated constraints===========================\n")
        file.write(constraints)
        formula_prompt = f"""
        Your task is to convert each constaint you identified previously from a tax into cvc5 
        smt formulas. Given the form {text}, please generate cvc5 smt formulas for the following extract constraints: {constraints} 
        """
        formulas = gpt_infer(formula_prompt)
        print(formulas)
        #file.write("===================prompt===========================\n")
        #file.write(formula_prompt)
        file.write("===================generated formulas===========================\n")
        file.write(formulas)      
        
        
extract_tax_requirement(TAX_RESULT, FORM_2848, FORM_2848_NAME)
extract_tax_requirement(TAX_RESULT, FORM_iw7, FORM_iw7_NAME)
extract_tax_requirement(COMPLIANCE_RESULT, FINRA_2090, FINRA_2090_NAME)
extract_tax_requirement(COMPLIANCE_RESULT, FINRA_2111, FINRA_2111_NAME)