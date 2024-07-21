import argparse
import os
import openpyxl
import json
import time
import sys
import pandas as pd
from formulas.parse_requirements import ms_to_smt
from schema.requirements_formula import (
        check_breadth,
        check_foundations,
        check_significant_implementation,
        check_artificial_depth,
        check_electives, 
        check_additional)
from schema.process import process, agent_prompt, RESULTS_DIR
 

def run_agent(name, req, transcript_path, trace):
        time.sleep(180) #prevent token length limit issue
        if len(trace)>500:
                short_trace = trace[0:500]
        else:
                short_trace = trace
        policy = agent_prompt(name, req, transcript_path, short_trace)
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
        
        
def run_analysis(transcript_path, requirement_doc):  
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
        print(f"We obtained the following result from solving foundations requirement constraints: \n")
        print(foundations_result)
        if foundations_result.isSat()==False:
                print(run_agent("foundations", requirement_dict["FOUNDATIONS REQUIERMENT"], transcript, foundations_trace))
        breadth_result, breadth_trace = check_breadth(transcript)
        print(f"We obtained the following result from solving breadth requirement constraints: \n")
        print(breadth_result)
        if breadth_result.isSat()==False:
                print(run_agent("breadth", requirement_dict["BREADTH REQUIREMENT"], transcript, breadth_trace))
        significant_implementation_result, significant_implementation_trace = check_significant_implementation(transcript)
        print(f"We obtained the following result from solving significant_implementation  requirement constraints: \n")
        print(significant_implementation_result)
        if significant_implementation_result.isSat()==False:
                print(run_agent("significant_implementation", requirement_dict["SIGNIFICANT IMPLEMENTATION REQUIREMENT"], transcript, significant_implementation_trace))
        depth_result, depth_trace = check_artificial_depth(transcript)
        print(f"We obtained the following result from solving depth requirement constraints: \n")
        print(depth_result)
        if depth_result.isSat()==False:
                print(run_agent("depth", requirement_dict["ARTIFICIAL INTELLEGIENCE DEPTH"], transcript, depth_trace))
        electives_result, electives_trace = check_electives(transcript)
        print(f"We obtained the following result from solving elective requirement constraints: \n")
        print(electives_result)
        if electives_result.isSat()==False:
                print(run_agent("elective", requirement_dict["ELECTIVES"], transcript, electives_trace))
        additional_result, additional_trace = check_additional(transcript)
        print(f"We obtained the following result from solving additionaal requirement constraints: \n")
        print(additional_result)
        if additional_result.isSat()==False:
                print(run_agent("additional", requirement_dict["ADDITIONAL REQUIREMENT"], transcript, additional_trace))
                
def parse_arguments(args):
        parser = argparse.ArgumentParser(sys.argv[0])
        parser.add_argument('--t', type=str, required=True, help="Please uploading a transcript", default="/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf")
        parser.add_argument('--r', type=str, required=True, help="Please uploading a requirement document", default='./program_sheets/Stanford_AI_MS.pdf')
        args = parser.parse_args()
        return parser.parse_args()

def main():
        args = parse_arguments(sys.argv[1:])
        print(run_analysis(args.t, args.r))

        
if __name__ == "__main__":
        main()
        
        