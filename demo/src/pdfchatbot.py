import sys
import yaml
import fitz
import gradio as gr
from openai import OpenAI
sys.path.append("/home/sallyjunsongwang/courseSAT")
from parse_input import gpt_parse_transcript

class PDFChatBot:
    def __init__(self):
        """
        Initialize the PDFChatBot instance.

        Parameters:
            config_path (str): Path to the configuration file (default is "../config.yaml").
        """
        self.processed = False
        self.page = 0
        self.chat_history = []
        self.documents = None


    def add_text(self, history, text):
        """
        Add user-entered text to the chat history.

        Parameters:
            history (list): List of chat history tuples.
            text (str): User-entered text.
        Returns:
            list: Updated chat history.
        """
        history = "annalyzing transcript using smt solver and llm..."
        return history

    def generate_response(self, history, query, file):
        """
        Generate a response based on user query and chat history.

        Parameters:
            history (list): List of chat history tuples.
            query (str): User's query.
            file (FileStorage): The uploaded PDF file.

        Returns:
            tuple: Updated chat history and a space.
        """
        if not query:
            raise gr.Error(message='Submit a question')
        if not file:
            raise gr.Error(message='Upload a PDF')
        if not self.processed:
            self.process_file(file)
            self.processed = True
        out, history = gpt_parse_transcript(file)
        result = out
        self.chat_history.append(f"satisfiable requirements? {history}")
        return history, out

    def render_file(self, file):
        """
        Renders a specific page of a PDF file as an image.

        Parameters:
            file (FileStorage): The PDF file.

        Returns:
            PIL.Image.Image: The rendered page as an image.
        """
        output = ""
        out, SAT, why = gpt_parse_transcript(file)
        for i in out:
            output += f"========each course analyzed by GPT and Solver: {i}============\n"
        output += f"********course requirements satisfied? {SAT}, {why}************"
        return  output