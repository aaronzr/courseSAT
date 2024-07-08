import argparse
import os
import openpyxl
import json
import sys
import pygsheets
import gspread
import pandas as pd
from oauth2client.service_account import ServiceAccountCredentials
from schema.requirements_formula import  check_artificial_depth

def get_worksheet(credentials): 
        scope = ['https://spreadsheets.google.com/feeds','https://www.googleapis.com/auth/drive']
        creds = ServiceAccountCredentials.from_json_keyfile_name('./credentials.json', scope)
        client = gspread.authorize(creds)
        SAMPLE_RANGE_NAME = "GenieWS_requirements"
        sheet = client.open("GenieWS_requirements")
        course_sheet = sheet.get_worksheet(0)
        df = pd.DataFrame.from_dict(course_sheet.get_all_records())
        print(df.head())
        return df, sheet 

def run_analysis(transcript, requirement_doc, specification): 
        result = check_artificial_depth(transcript)
        return result

def tell_agent(credentials, df, sheet, transcript_path, requirement_doc, specification): 
        with open(transcript_path, 'r') as file:
                transcript = json.load(file)
        result = run_analysis(transcript, requirement_doc, specification)
        df = pd.DataFrame(df)
        if result.isSat() == False: 
                new_row = pd.DataFrame({'Kind': ["Internal"]})
                new_row = pd.DataFrame({"Type": ["str"]})
                new_row = pd.DataFrame({"Name": ["str"]})
                new_row = pd.DataFrame({"Enum Values": ["MS AI"]})
                new_row = pd.DataFrame({"Description": [f"{specification} is not met"]})
                new_row = pd.DataFrame({"Action": [f"if self.ArtificialIntelligenceCourseTaken == False: >say('You need to take more AI depth courses to satisfy requirements')"]})
                df = pd.concat([df, new_row], ignore_index=True)
        print(df.tail(1))
        client = gspread.authorize(credentials)
        #sheet.add_worksheet(rows=df.shape[0],cols=df.shape[1],title=f"{specification.replace('', '_').lower()}")
        #new_action_sheet = sheet.get_worksheet(1)
        #new_action_sheet.insert_rows(df.head(1).values.tolist())
        file_name = 'policy.xlsx'
        df.to_excel(file_name)
        
  
                

def parse_arguments(args):
        parser = argparse.ArgumentParser(sys.argv[0])
        parser.add_argument('--t', type=str, required=False, default='./schema_results/stanford_transcript1.json')
        parser.add_argument('--r', type=str, required=False, default='./program_sheets/Stanford_AI_MS.pdf')
        parser.add_argument('--s', type=str, required=False, default='FOUNDATIONS REQUIREMENT')
        args = parser.parse_args()
        return parser.parse_args()

def main():
        args = parse_arguments(sys.argv[1:])
        if args.t == True: 
                pass
        if args.r == True:
                pass
        creds = ServiceAccountCredentials.from_json_keyfile_name('credentials.json')
        df, sheet = get_worksheet(creds)
        tell_agent(creds, df, sheet, args.t, args.r, args.s)
main()
        
        