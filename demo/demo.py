from openai import AsyncOpenAI
import chainlit as cl
import json, os, asyncio

api_key = os.getenv("OPENAI_API_KEY")
client = AsyncOpenAI(api_key=api_key)


@cl.on_chat_start
async def on_chat_start():
    files = None

    # Wait for the user to upload a file
    while files == None:
        files = await cl.AskFileMessage(
            content="Please upload a text file to begin!",
            accept=["application/pdf"],
            max_size_mb=20,
            timeout=180,
        ).send()

    file = files[0]

    msg = cl.Message(
        content=f"Creating chunks for `{file.name}`...", disable_human_feedback=True
    )
    await msg.send()

    # Write the file to local file system
    if not os.path.exists("tmp"):
        os.makedirs("tmp")
    with open(f"tmp/{file.name}", "wb") as f:
        f.write(file.content)

    pdf_loader = PyPDFLoader(file_path=f"tmp/{file.name}")

    # Split the text into chunks
    documents = pdf_loader.load_and_split(text_splitter=text_splitter)



@cl.on_chat_start
def start_chat():
    cl.user_session.set(
        "message_history",
        [{"role": "system", "content": "You are a helpful assistant."}],
    )

@cl.set_starters
async def set_starters():
    return [
        cl.Starter(
            label="Translate Course Requirements",
            message="Please translate Stanford MS AI course requirements into SMT formulas",
            icon="/public/write.svg",
            ),
        cl.Starter(
            label="Translate FINRA Rules",
            message="Make a data analysis on the next CSV file I will upload.",
            icon="/public/write.svg",
            )
        ]

@cl.on_message
async def run_conversation(message: cl.Message):
    message_history = cl.user_session.get("message_history")
    message_history.append({"role": "user", "content": message.content})
    # Step 1: send the conversation and available functions to the model
    
    msg = cl.Message(author="Assistant", content="")
    await msg.send()

    response = await client.chat.completions.create(
        model="gpt-4o",
        messages=message_history,
    )
    response_message = response.choices[0].message

    msg.content = response_message.content or ""
    await msg.update()
    
    
    