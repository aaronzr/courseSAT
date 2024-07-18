from translate import (
        pdf_to_text,
        gpt_infer
)


transcript_path = "/home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf"
requirement_path = "../program_sheets/Stanford_AI_MS.pdf"

def find_IR(requirement_path, transcript_path):
        requirement = pdf_to_text(requirement_path)
        transcript = pdf_to_text(transcript_path)
        example = open("./IR_notes_10.txt", "r")
        prompt = f"""
        Your task is to identify a precise, formal, and rigorous intermediate representation that
        will faciliate building a semantic parser that can parse natural langauge into formal language
        in a given course requirement sheet and a given transcript. The formal intermediate representaton 
        will be used for compiler construction later on. Please also pay atttention to faculty approval and additional requirements
        in the requirements in your intermedate representation. Here is the course requirement document: {requirement} and transcript: {transcript}. 
        You can consider entity, relations, constraints, functions, etc and this is an example output: {example.read()}.
        Remember, you should pay atttention to faculty approval and additional requirements and all constraints in requirement document: {requirement} and transcript: {transcript}. Please generate formal semantics of intermediate representation only.      
        """
        out = gpt_infer(prompt)
        print(out)
        print("=======================================\n")     
        prompt2 = f"""
        Your task is to generate python code that can automacally parse a given intermediate representation
        into an abstract syntax tree. The purrpose of the abstract syntax tree is for a compiler to generate correct cvc5 solver formulas in python that fully capture complex constraints 
        in a given course requirement sheet and a given transcript. Here is the course requirement document: {requirement} and transcript: {transcript}. Here is the 
        possible intermediate representation previously identified by you: {out}. 
        You do not need to worry about compiler structure for now. 
        Please use the semantics of intermediate representation to generate python code that can automacally parse a given intermediate representation
        into an abstract syntax tree.
        """
        out2 = gpt_infer(prompt2)
        print(out2)
        print("=======================================\n")       
        prompt3 = f"""
        Your task is to write a compiler that can automatcally generate CORRECT cvc5 solver formulas code based 
        on the constraints in the abstract syntax tree previously identified by you. Below is a sample cvc5 solver formulas code the compiler should generate.
        ```python 
        def check_stanford_master_elective_requirements(seminar_choices, other_electives):
    # Initialize solver
    solver = cvc5.Solver()
    solver.setOption("produce-unsat-cores", "true")
    solver.setOption("produce-models", "true")
    solver.setOption("produce-proofs", "true")
    solver.setLogic("ALL")
     # Create a variable for each seminar representing whether it is counted (1) or not (0)
    seminar_vars = create_course_vars_and_constraints(solver, seminar_choices, seminar_choices)
    elective_vars = create_course_vars_and_constraints(solver, other_electives, other_electives)
    
    # Create the formula for the sum of the units of 1-2 unit seminars
    unit_sum = solver.mkInteger(0)
    for seminar, (taken, units, grade) in seminar_choices.items():
        if 1 <= units <= 2:
            # Add a constraint that the variable can only be 0 or 1
            solver.assertFormula(solver.mkTerm(Kind.OR,
                solver.mkTerm(Kind.EQUAL, seminar_vars[seminar+"_units"], solver.mkInteger(0)),
                solver.mkTerm(Kind.EQUAL, seminar_vars[seminar+"_units"], solver.mkInteger(1))
            ))
            # Add the units to the sum
        unit_sum = solver.mkTerm(Kind.ADD, unit_sum, solver.mkTerm(Kind.MULT, seminar_vars[seminar+"_units"], solver.mkInteger(units)))

    # Assert that the sum of the units of 1-2 unit seminars is less than or equal to 3
    solver.assertFormula(solver.mkTerm(Kind.LEQ, unit_sum, solver.mkInteger(3)))
    ```
        The compiler should output a list of courses used to satisfied all constraints or output a list of courses not saisfied given the constraints. Given your intermediate representation: {out} and abstract syntax tree:{out2} for the
        trranscript: {transcript} and course requirements: {requirement}, 
        please generate compiler code that compiles an example AST of {out2} into CORRECT cvc5 solver formulas to check satisfiability of constraints. Remember, You MUST generate a compiler that can generate CORRECT cvc5 solver formulas code based on an example AST of {out2}. 
        """
        out3 = gpt_infer(prompt3)
        print("=======================================\n")
        print(out3)
        file = open(f"IR_notes_12.txt", 'w+')
        file.write(out)
        file.write("=======================================\n")
        file.write(out2)
        file.write("=======================================\n")
        file.write(out3)
        file.write("=======================================\n")
        file.close()
        
find_IR(requirement_path, transcript_path)