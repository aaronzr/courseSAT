```
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
export OPENAI_API_KEY='<your-api-key>'
python main.py --t /home/sallyjunsongwang/courseSAT/transcripts/stanford_transcript1.pdf --r ./program_sheets/Stanford_AI_MS.pdf
```
Demo
```
chainlit run demo.py -w
```
