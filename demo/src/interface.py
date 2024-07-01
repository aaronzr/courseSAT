import gradio as gr

# Gradio application setup
def create_demo():
    with gr.Blocks(title= "smt solver powered course requirement analysis",
        theme = "Soft"
        ) as demo:
        with gr.Column():
            with gr.Row():
                chat_history = gr.Chatbot(value=[], elem_id='smt solver powered course requirement analysis', height=400)

        with gr.Row():
            with gr.Column(scale=3):
                text_input = gr.Textbox(
                    show_label=True,
                    placeholder="Type here to specify a requirement you'd like to check",
                container=False)

            with gr.Column(scale=2):
                submit_button = gr.Button('Send')

            with gr.Column(scale=2):
                uploaded_pdf = gr.UploadButton("📁 Upload PDF", file_types=[".pdf"])
                

        return demo, chat_history, text_input, submit_button, uploaded_pdf

if __name__ == '__main__':
    demo, chatbot, text_input, submit_button, uploaded_pdf  = create_demo()
    demo.queue()
    demo.launch()
