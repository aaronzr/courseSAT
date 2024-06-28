import os
import openai
from openai import OpenAI
from translate import (
	gpt_infer, 
	get_AI_requirements,
	pdf_to_text)

BASELINE_DIR = "../zero_shot_baseline"
SYNTHETIC_BASELINE_DIR = "../zero_shot_baseline/synthetic"

#all in one prompt: transcript first, requirements later;
#transcript first -> BS requirement
#transcrript again -> MS requiement
def end_to_end_evaluation_a(dir, transcript_path, synthetic):
	transcript_name = os.path.basename(transcript_path)
	BS_core_requiements, BS_AI_elective, BS_senior_project_requiements, MS_AI = get_AI_requirements()
	if synthetic is False: 
		transcript = pdf_to_text(transcript_path)
	transcript_file = open(transcript_path, "r")
	transcript = transcript_file.read()
	prompt_a =  f"""
	Your task is to identify whether a given student's transcript satisfies specific degree requirements, which will also be given to you. 
 	Please analyze and understand the student transcript: {transcript}, as well as the following BS core requirements: {BS_core_requiements}, 
 	BS senior project requirements: {BS_senior_project_requiements}, BS AI elective requirements: {BS_AI_elective}. If all BS requirements are satisfied,
	please output "BS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript. If  all BS requirements are satisfied, 
	please further analyze and understand the student transcript: {transcript} as well as the MS specialization requirements: {MS_AI}. If all MS requirements are satisfied,
	please output "MS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript.
	"""
	zero_shot_answer_a = gpt_infer(prompt_a)
	print(zero_shot_answer_a)
	file = open(f"{dir}/{os.path.splitext(transcript_name)[0]}_zero_shot_a.txt", 'w+')
	file.write(zero_shot_answer_a)
	file.close()

#all in one prompt: swapping order this time - requirements first, transcript used once later 
#BS, MS requirements first -> transcript
def end_to_end_evaluation_b(dir, transcript_path, synthetic):
	transcript_name = os.path.basename(transcript_path)
	BS_core_requiements, BS_AI_elective, BS_senior_project_requiements, MS_AI = get_AI_requirements()
	if synthetic is False: 
		transcript = pdf_to_text(transcript_path)
	transcript_file = open(transcript_path, "r")
	transcript = transcript_file.read()
	prompt_b =  f"""
	Your task is to identify whether a given student's transcript satisfies specific degree requirements, which will also be given to you.
	BS core requirements: {BS_core_requiements}, BS senior project requirements: {BS_senior_project_requiements}, BS AI elective requirements: {BS_AI_elective}, 
	MS specialization requirements: {MS_AI}. Please analyze and understand the student transcript: {transcript}. If all BS requirements are satisfied,
	please output "BS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript. If all BS requirements are satisfied, 
	please further analyze the transcript given MS specialization requirements.  If all MS requirements are satisfied,
	please output "MS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript.
	"""
	zero_shot_answer_b = gpt_infer(prompt_b)
	print(zero_shot_answer_b)
	file = open(f"{dir}/{os.path.splitext(transcript_name)[0]}_zero_shot_b.txt", 'w+')
	file.write(zero_shot_answer_b)
	file.close()

#all in one prompt: swapping order this time - requirements first, transcript used twice later 
#BS requirements -> transcript
#MS requirements -> transcript
def end_to_end_evaluation_c(dir, transcript_path, synthetic):
	transcript_name = os.path.basename(transcript_path)
	BS_core_requiements, BS_AI_elective, BS_senior_project_requiements, MS_AI = get_AI_requirements()
	if synthetic is False: 
		transcript = pdf_to_text(transcript_path)
	transcript_file = open(transcript_path, "r")
	transcript = transcript_file.read()
	prompt_c =  f"""
	Your task is to identify whether a given student's transcript satisfies specific degree requirements, which will be provided next.
	BS core requirements: {BS_core_requiements}, BS senior project requirements: {BS_senior_project_requiements}, BS AI elective requirements: {BS_AI_elective}, 
	Please analyze and understand the student transcript: {transcript}. If all BS requirements are satisfied,
	please output "BS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript. If all BS requirements are satisfied, here are MS specialization requirements: {MS_AI}.  
	Given MS specialization requirements, please further analyze the transcript: {transcript}.  If all MS requirements are satisfied,
	please output "MS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript.
	"""
	zero_shot_answer_c = gpt_infer(prompt_c)
	print(zero_shot_answer_c)
	file = open(f"{dir}/{os.path.splitext(transcript_name)[0]}_zero_shot_c.txt", 'w+')
	file.write(zero_shot_answer_c)
	file.close()

#two separate prompts to break down if else stataement 
#first_prompt: BS requirements->transcript
#second_prompt: MS requirements->transcript
def end_to_end_evaluation_d(dir, transcript_path, synthetic):
	transcript_name = os.path.basename(transcript_path)
	BS_core_requiements, BS_AI_elective, BS_senior_project_requiements, MS_AI = get_AI_requirements()
	if synthetic is False: 
		transcript = pdf_to_text(transcript_path)
	transcript_file = open(transcript_path, "r")
	transcript = transcript_file.read()
	prompt_one =  f"""
	Your task is to identify whether a given student's transcript satisfies bachelor in science (BS) degree requirements, which will also be given to you.
	BS core requirements: {BS_core_requiements}, BS senior project requirements: {BS_senior_project_requiements}, BS AI elective requirements: {BS_AI_elective}. 
	Please analyze and understand the student transcript: {transcript}. If all BS requirements are satisfied,
	please output "BS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript.
	"""
	zero_shot_answer_one = gpt_infer(prompt_one)
 
	prompt_two =  f"""
	Your task is to identify whether a given student's transcript satisfies master in science (MS) degree requirements, which will be given to you.
	Here are MS specialization requirements: {MS_AI}. 
	Please analyze and understand the student transcript: {transcript}. If all MS requirements are satisfied,
	please output "MS SAT". Otherwise, please output a list of courses not satisfied based on the student's transcript.
	"""
	zero_shot_answer_two = gpt_infer(prompt_two)
	file = open(f"{dir}/{os.path.splitext(transcript_name)[0]}_zero_shot_d.txt", 'w+')
	file.write("========================GPT Answer to Prompt One Regarding BS Requirements====================\n")
	file.write(zero_shot_answer_one)
	file.write("========================GPT Answer to Prompt Two Regarding MS Requirements====================\n")
	file.write(zero_shot_answer_two)
	file.close()

def evluate_benchmark(folder, synthetic=True):
	count = 0
	for path, folders, files in os.walk(folder):
		for filename in files:
			count += 1
			transcript_path = os.path.join(folder, filename)
			results_directory = f"{SYNTHETIC_BASELINE_DIR}/{count}"
			if not os.path.exists(results_directory):
				os.makedirs(results_directory)
				end_to_end_evaluation_a(results_directory, transcript_path, synthetic)
				end_to_end_evaluation_b(results_directory, transcript_path, synthetic)
				end_to_end_evaluation_c(results_directory, transcript_path, synthetic)
				end_to_end_evaluation_d(results_directory, transcript_path, synthetic)



if __name__ == "__main__":
	#translate_to_formal_statements(doc="../Stanford_AI.pdf", requirement='SIGNIFICANT IMPLEMENTATION REQUIREMENT')
	#transcript = "/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf"
	folder = "/home/sallyjunsongwang/courseSAT/transcripts/synthetic"
	evluate_benchmark(folder)