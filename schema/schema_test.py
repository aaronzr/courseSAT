import os
import sys
import json
import argparse

def parse_schema(schema_path):
        with open(schema_path, 'r') as file:
                data = json.load(file)
        name = os.path.basename(schema_path)
        transcript_name, _ = name.split(".")
        student = data.get("Student", {})
        ap_credits = data.get("AP_Credits", [])
        courses_taken = data.get("Courses_Taken", [])
        approval = data.get("Approval", [])
        deviations = data.get("Deviations", [])
        cumulative_gpa = data.get("Cumulative_GPA", {})

        # Accessing student information
        student_name = student.get("Name")
        student_program = student.get("Program")
        student_id = student.get("StudentID")
        student_coterm = student.get("Coterm")

        print(f"Student Name: {student_name}, Program: {student_program}, ID: {student_id}, Coterm: {student_coterm}")

        # Accessing AP Credits
        for credit in ap_credits:
                advanced_placement = credit.get("Advanced_Placement")
                earned_units = credit.get("Earned_Units")
                print(f"AP Credit: {advanced_placement}, Earned Units: {earned_units}")

        # Accessing Courses Taken
        for course in courses_taken:
                course_id = course.get("Course_ID")
                title = course.get("Title")
                earned_units = course.get("Earned_Units")
                grade = course.get("Grade")
                print(f"Course ID: {course_id}, Title: {title}, Earned Units: {earned_units}, Grade: {grade}")

        # Accessing Approval Information
        for app in approval:
                approved = app.get("Approved")
                approved_by = app.get("Approved_By")
                approved_course_id = app.get("Approved_Course_ID")
                print(f"Approved: {approved}, Approved By: {approved_by}, Approved Course ID: {approved_course_id}")

        # Accessing Approval Information
        for dev in deviations:
                approved_by = app.get("Approved_By")
                dev_ourse_id = app.get("Deviated_Course_ID")
                print(f"deviations: {dev}, Approved By: {approved_by}, Deviated Course ID: {dev_ourse_id}")
        # Accessing Cumulative GPA
        undergrad_gpa = cumulative_gpa.get("Undergrad")
        graduate_gpa = cumulative_gpa.get("Graduate")

        print(f"Undergrad GPA: {undergrad_gpa}, Graduate GPA: {graduate_gpa}")
        return student, ap_credits, courses_taken, approval, cumulative_gpa

def parse_arguments(args):
        parser = argparse.ArgumentParser(sys.argv[0])
        parser.add_argument('--t', type=str, required=False, default='../schema_results/stanford_transcript1.json')
        args = parser.parse_args()
        return parser.parse_args()

def main():
        args = parse_arguments(sys.argv[1:])
        print(parse_schema(args.t))

        
if __name__ == "__main__":
        main()