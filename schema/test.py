transcript_depth_test = {
	"Student": {"Name": "John Doe", "Program": "AI", "StudentID": 12345, "Coterm": False},
	"AP_Credits": [],
	"Courses_Taken": [
		{"Course_ID": "CS 221", "Title": "Artificial Intelligence: Principles and Techniques", "Earned_Units": 3, "Grade": "A"},
		{"Course_ID": "CS 223A", "Title": "Introduction to Robotics", "Earned_Units": 3, "Grade": "B"},
		{"Course_ID": "CS 224N", "Title": "Natural Language Processing", "Earned_Units": 4, "Grade": "A-"},
		{"Course_ID": "CS 229", "Title": "Machine Learning", "Earned_Units": 3, "Grade": "B+"},
		{"Course_ID": "CS 399", "Title": "Independent Research", "Earned_Units": 6, "Grade": "A"},
	],
	"Deviations": [],
	"Approval": [],
	"Cumulative_GPA": {"Undergrad": 3.8, "Graduate": 3.9},	
	}

transcript_elective_test = {
    "Student": {
        "Name": "John Doe",
        "Program": "MSCS", 
        "StudentID": 123456789,
        "Coterm": False
    },
    "AP_Credits": [
        {"Advanced_Placement": "AP Calculus", "Earned_Units": 9}          
    ],
    "Courses_Taken": [
        {"Course_ID": "CS 221", "Title": "Artificial Intelligence", "Earned_Units": 3, "Grade": "A"},
        {"Course_ID": "CS 110", "Title": "Programming Abstractions", "Earned_Units": 5, "Grade": "A-"},
        {"Course_ID": "ENG 300A", "Title": "Special Topics in Engineering", "Earned_Units": 2, "Grade": "B+"},
        {"Course_ID": "CS 129", "Title": "Machine Learning", "Earned_Units": 3, "Grade": "B"},
        {"Course_ID": "CS 229", "Title": "Machine Learning", "Earned_Units": 3, "Grade": "B+"},
    ],
    "Deviations": [
        {
            "Deviated_Course_ID": "CS 150",
            "Approved": True,
            "Approved_By": "Prof. XYZ"
        }
    ],
    "Approval": [
        {
            "Approved": True,
            "Approved_By": "Prof. XYZ",
            "Approved_Course_ID": "ENG 300A"
        }
    ],    
    "Cumulative_GPA": {
        "Undergrad": 3.8,
        "Graduate": 3.9,
    }
}