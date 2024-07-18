import argparse
import os
import openpyxl
import json
import sys
import pygsheets
import gspread
import pandas as pd
from formulas.parse_requirements import ms_to_smt
from schema.requirements_formula import (
        check_breadth,
        check_foundations,
        check_significant_implementation,
        check_artificial_depth,
        check_electives)
from schema.process import process

DIR = "./schema_results"

def run_analysis(transcript_path, requirement_doc):
        
        print("Let's first translate the uploaded document into SMT fomulas...\n") 
        reqs, req_out, formulas = ms_to_smt(requirement_doc)
        for i in range(len(reqs)):
                print(f"for {reqs[i]} in the document, we first break it down to {req_out[i]},\
                      and then we have the following formulas: \n")
                print(formulas[i])    
        print("Let's parse the given transcript into a json schema...\n")  
        transcript = process(transcript_path)
        foundations_result = check_foundations(transcript)
        print(f"We obtained the following result from solving foundations requirement constraints: \n")
        print(foundations_result)
        breadth_result = check_breadth(transcript)
        print(f"We obtained the following result from solving breadth requirement constraints: \n")
        print(breadth_result)
        significant_implementation_result = check_significant_implementation(transcript)
        print(f"We obtained the following result from solving significant_implementation  requirement constraints: \n")
        print(significant_implementation_result)
        depth_result = check_artificial_depth(transcript)
        print(f"We obtained the following result from solving depth requirement constraints: \n")
        print(depth_result)
        electives_result = check_electives(transcript)
        print(f"We obtained the following result from solving elective requirement constraints: \n")
        print(electives_result)
                

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
        
        