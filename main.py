import argparse
import os
import openpyxl
import json
import time
import sys
import pandas as pd
from formulas.parse_requirements import (
        ms_to_smt, backend_auto_formulas_gen)
from schema.requirements_formula import (
        check_breadth,
        check_foundations,
        check_significant_implementation,
        check_artificial_depth,
        check_electives, 
        check_additional)
from schema.process import process, agent_prompt, RESULTS_DIR
from schema.requirements_formula import gpt4_infer
EVAL_DIR_1 = "eval/definitions_only"
EVAL_DIR_2 = "eval/requirements_only"
EVAL_DIR_3 = "eval/definitions_and_reqs"


def run_agent(name, req, transcript_path, result, trace):
        filler = ""
        policy = agent_prompt(name, req, transcript_path, filler, result, trace, use_verbal=False, use_both=False)
        print(req)
        start = "```"
        start2 = "```python"
        end = "```"
        if start in policy: 
                fixed_policy = policy.split(start)[1].split(end)[0]
        if start2 in policy: 
                fixed_policy = policy.split(start2)[1].split(end)[0]
        else:
                fixed_policy = policy
        policy_file = open(f"{name}_policy.txt", "w+")
        policy_file.write(fixed_policy)
        policy_file.close()
        print("==================agent policy generated given solver results=====================\n")
        print(fixed_policy)

def run_agent_by_verbalized_core(name, req, transcript_path, verbal_formulas, result):
        filler = ""
        policy = agent_prompt(name, req, transcript_path, verbal_formulas, result, filler, use_verbal=True, use_both=False)
        print(req)
        start = "```"
        start2 = "```python"
        end = "```"
        if start in policy: 
                fixed_policy = policy.split(start)[1].split(end)[0]
        if start2 in policy: 
                fixed_policy = policy.split(start2)[1].split(end)[0]
        else:
                fixed_policy = policy
        policy_file = open(f"verbalizedCore_{name}_policy.txt", "w+")
        policy_file.write(fixed_policy)
        policy_file.close()
        print("==================agent policy generated given solver results=====================\n")
        print(fixed_policy)   
        
def run_agent_by_both(name, req, transcript_path, verbal_formulas, result, trace):
        policy = agent_prompt(name, req, transcript_path, verbal_formulas, result, trace, use_verbal=False, use_both=True)
        print(req)
        start = "```"
        start2 = "```python"
        end = "```"
        if start in policy: 
                fixed_policy = policy.split(start)[1].split(end)[0]
        if start2 in policy: 
                fixed_policy = policy.split(start2)[1].split(end)[0]
        else:
                fixed_policy = policy
        policy_file = open(f"traceANDverbalcore_{name}_policy.txt", "w+")
        policy_file.write(fixed_policy)
        policy_file.close()
        print("==================agent policy generated given solver results=====================\n")
        print(fixed_policy)    
        
def run_analysis(transcript_path, requirement_doc):  
        breath_background = open("prompts/breath_background.prompt", "r")
        foundation_background = open("prompts/foundation_background.prompt", "r")
        sig_impl_background = open("prompts/sig_impl_background.prompt", "r")
        defintion_list = [breath_background.read(),  \
                foundation_background.read(),\
                sig_impl_background.read()]
        print("Let's first translate the uploaded document into SMT fomulas...\n") 
        reqs, req_out, formulas = ms_to_smt(requirement_doc)
        requirement_dict = dict(zip(reqs, req_out))
        for i in range(len(reqs)):
                print(f"for {reqs[i]} in the document, we first break it down to {req_out[i]},\
                      and then we have the following formulas: \n")
                print(formulas[i])    
        print("Let's parse the given transcript into a json schema...\n")  
        name = os.path.basename(transcript_path)
        transcript_name, _ = name.split(".")
        path = f"{RESULTS_DIR}/{transcript_name}.json"
        if os.path.isfile(path):
                transcript = path
        else:      
                transcript = process(transcript_path)
        foundations_result, foundations_trace = check_foundations(transcript)
        breadth_result, breadth_trace = check_breadth(transcript)
        significant_implementation_result, significant_implementation_trace = check_significant_implementation(transcript)
        definition_mappings = zip(
                ["BREADTH", "FOUNDATIONS", "SIGNIFICANT IMPLEMENTATION"],
                defintion_list, 
                [requirement_dict["BREADTH REQUIREMENT"], requirement_dict["FOUNDATIONS REQUIERMENT"], requirement_dict["SIGNIFICANT IMPLEMENTATION REQUIREMENT"]],
                [breadth_result, foundations_result, significant_implementation_result],
                [breadth_trace, foundations_trace, significant_implementation_trace])
        first_counter = 0
        for req_name, definition, req, result, formula in definition_mappings: 
                first_prompt = f"""
                You are a seasoned SMT formulas to natural language translator. You will be provided 
                with smt core formulas and definitions of variables used in those formulas, which the
                smt solver tries to solve for. Given the definitions of variables used in the formula: {definition},
                please faithfully translate the following SMT formulas into 
                natural languages: {formula}
                """
                verbalized_formulas = gpt4_infer(first_prompt)
                run_agent_by_verbalized_core(req_name, req, transcript, verbalized_formulas, result)         
                run_agent_by_both(req_name, req, transcript, verbalized_formulas, result, formula)
          
        print(f"We obtained the following result from solving foundations requirement constraints: \n")
        print(run_agent("foundations", requirement_dict["FOUNDATIONS REQUIERMENT"], transcript, foundations_result, foundations_trace))
        print(f"We obtained the following result from solving breadth requirement constraints: \n")

        print(run_agent("breadth", requirement_dict["BREADTH REQUIREMENT"], transcript, breadth_result, breadth_trace))
        print(f"We obtained the following result from solving significant_implementation  requirement constraints: \n")
        print(significant_implementation_result)
        print(run_agent("significant_implementation", requirement_dict["SIGNIFICANT IMPLEMENTATION REQUIREMENT"], transcript, significant_implementation_result, significant_implementation_trace))
        '''
        depth_result, depth_trace = check_artificial_depth(transcript)
        print(f"We obtained the following result from solving depth requirement constraints: \n")
        print(depth_result)

        print(run_agent("depth", requirement_dict["ARTIFICIAL INTELLEGIENCE DEPTH"], transcript, depth_result, depth_trace))
        electives_result, electives_trace = check_electives(transcript)
        print(f"We obtained the following result from solving elective requirement constraints: \n")
        print(electives_result)
        print(run_agent("elective", requirement_dict["ELECTIVES"], transcript, electives_result, electives_trace))
        additional_result, additional_trace = check_additional(transcript)
        print(f"We obtained the following result from solving additionaal requirement constraints: \n")
        print(additional_result)
        print(run_agent("additional", requirement_dict["ADDITIONAL REQUIREMENT"], transcript, additional_result, additional_trace))
        '''
def parse_arguments(args):
        parser = argparse.ArgumentParser(sys.argv[0])
        parser.add_argument('--t', type=str, required=True, help="Please uploading a transcript", default="/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf")
        parser.add_argument('--r', type=str, required=True, help="Please uploading a requirement document", default='./program_sheets/Stanford_AI_MS.pdf')
        args = parser.parse_args()
        return parser.parse_args()

def run_verbalization_eval(transcript_path, requirement_doc):
        breath_background = open("prompts/breath_background.prompt", "r")
        foundation_background = open("prompts/foundation_background.prompt", "r")
        sig_impl_background = open("prompts/sig_impl_background.prompt", "r")
        defintion_list = [breath_background.read(),  \
                foundation_background.read(),\
                sig_impl_background.read()]
        if os.path.exists(EVAL_DIR_1)==False:   
                os.mkdir(EVAL_DIR_1)
        if os.path.exists(EVAL_DIR_2)==False:   
                os.mkdir(EVAL_DIR_2)
        if os.path.exists(EVAL_DIR_3)==False:   
                os.mkdir(EVAL_DIR_3)
        name = os.path.basename(transcript_path)
        transcript_name, _ = name.split(".")
        path = f"{RESULTS_DIR}/{transcript_name}.json"
        if os.path.isfile(path):
                transcript = path
        else:      
                transcript = process(transcript_path)
        print("Let's first translate the uploaded document into SMT fomulas...\n") 
        reqs, req_out, formulas = ms_to_smt(requirement_doc)
        requirement_dict = dict(zip(reqs, req_out))
        foundations_result, foundations_trace = check_foundations(transcript)
        breadth_result, breadth_trace = check_breadth(transcript)
        significant_implementation_result, significant_implementation_trace = check_significant_implementation(transcript)
        '''
        definition_mappings = zip(defintion_list, \
                [breadth_trace, foundations_trace, significant_implementation_trace])
        first_counter = 0
        for definition, formula in definition_mappings: 
                first_prompt = f"""
                You are a seasoned SMT formulas to natural language translator. You will be provided 
                with smt core formulas and definitions of variables used in those formulas, which the
                smt solver tries to solve for. Given the definitions of variables used in the formula: {definition},
                please faithfully translate the following SMT formulas into 
                natural languages: {formula}
                """
                out = gpt4_infer(first_prompt)
                print(out)
                file = open(f'{EVAL_DIR_1}/{first_counter}.txt', 'w+')
                file.write(first_prompt)
                file.write(f"\n======================response below==============================\n")
                file.write(out)
                file.close()
                first_counter += 1
                
        nl_mappings = zip([requirement_dict["BREADTH REQUIREMENT"], requirement_dict["FOUNDATIONS REQUIERMENT"], requirement_dict["SIGNIFICANT IMPLEMENTATION REQUIREMENT"]],\
        [breadth_trace, foundations_trace, significant_implementation_trace])
        second_counter = 0
        for definition,req, formula in full_mappings: 
                second_prompt = f"""
                You are a seasoned SMT formulas to natural language translator. You will be provided 
                with smt core formulas and relevant natural language requirements. Given natural language requirements: {req},
                please faithfully translate the following SMT formulas into natural languages: {formula}
                """
                out2 = gpt4_infer(third_prompt)
                print(out2)
                file = open(f'{EVAL_DIR_2}/{second_counter}.txt', 'w+')
                file.write(second_prompt)
                file.write(f"\n======================response below==============================\n")
                file.write(out2)
                file.close()
                second_counter += 1  
        ''' 
        full_mappings = zip(defintion_list, \
        [requirement_dict["BREADTH REQUIREMENT"], requirement_dict["FOUNDATIONS REQUIERMENT"], requirement_dict["SIGNIFICANT IMPLEMENTATION REQUIREMENT"]],\
        [breadth_trace, foundations_trace, significant_implementation_trace])
        third_counter = 0
        for definition,req, formula in full_mappings: 
                third_prompt = f"""
                You are a seasoned SMT formulas to natural language translator. You will be provided 
                with smt core formulas, definitions of variables used in those formulas, which the
                smt solver tries to solve for, and relevant natural language requirements. Given the definitions of variables used in the formula: {definition} and
                natural language requirements: {req},
                please faithfully translate the following SMT formulas into 
                natural languages: {formula}.
                """
                out3 = gpt4_infer(third_prompt)
                print(out3)   
                file = open(f'{EVAL_DIR_3}/{third_counter}.txt', 'w+')
                file.write(third_prompt)
                file.write(f"\n======================response below==============================\n")
                file.write(out3)
                file.close()
                
                fourth_prompt = f"""
                Your task is to identify any unfilled requirement given natural language requirement and verbalized smt formulas, which are previously verbalized by you. 
                You will be provided with verbalized fomulas and relevant natural language requirements. Given natural language requirements: {req} and 
                verbalized formulas {out3}, please identify specific unsatisfied courses, grades, or units. 
                """
                out4 = gpt4_infer(fourth_prompt)
                print(out4) 
                file = open(f'{EVAL_DIR_3}/{third_counter}_verbal2gap.txt', 'w+')
                file.write(fourth_prompt)
                file.write(f"\n======================response below==============================\n")
                file.write(out4)
                fifth_prompt = f"""
                Your task is to identify any unfilled requirement given natural language requirement and smt formulas. You will be provided 
                with smt core fomulas, definitions of variables used in those formulas, which the
                smt solver tries to solve for, and relevant natural language requirements. Given the definitions of variables used in the formula: {definition} and
                natural language requirements: {req}, and smt formulas: {formula}, please identify specific unsatisfied courses, grades, or units. 
                """
                out5 = gpt4_infer(fifth_prompt)
                print(out5)   
                
                file = open(f'{EVAL_DIR_3}/{third_counter}_ReqandFormulas2Gap.txt', 'w+')
                file.write(third_prompt)
                file.write(f"\n======================response below==============================\n")
                file.write(out5)
                file.close()                         
                third_counter += 1   

        
        
def main():
        args = parse_arguments(sys.argv[1:])
        #print(run_analysis(args.t, args.r))
        #print(run_verbalization_eval(args.t, args.r))
        sheets = ["Theory", "Info", "CompBio", "CompEng", "Indiv",\
                "Unspec", "VisComp", "Systems", "AI", "HCI"]
        counter = 0
        for sheet in sheets:
                if sheet in args.r:
                        backend_auto_formulas_gen(sheet)
        else:
                counter += 1
        if counter == 10:     
                print("Please upload a program sheet matching\
                        standard naming practice by the program.")

        
if __name__ == "__main__":
        main()
        
        