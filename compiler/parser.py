import json
from cvc5 import *

class Student:
    def __init__(self, student_id, name, email, degree_confer_date, is_HCP, is_Coterm):
        self.student_id = student_id
        self.name = name
        self.email = email
        self.degree_confer_date = degree_confer_date
        self.is_HCP = is_HCP
        self.is_Coterm = is_Coterm
        self.courses = []

    def add_course(self, course):
        self.courses.append(course)

class Course:
    def __init__(self, course_id, title, units, grade):
        self.course_id = course_id
        self.title = title
        self.units = units
        self.grade = grade
        self.satisfies_requirements = []

    def add_requirement(self, requirement):
        self.satisfies_requirements.append(requirement)

class ProgramRequirement:
    def __init__(self, requirement_id, description, required_units):
        self.requirement_id = requirement_id
        self.description = description
        self.required_units = required_units
        self.approvals = []

    def add_approval(self, approval):
        self.approvals.append(approval)

class Approval:
    def __init__(self, approval_id, approved_by, approval_date, note):
        self.approval_id = approval_id
        self.approved_by = approved_by
        self.approval_date = approval_date
        self.note = note

class EnrolledIn:
    def __init__(self, student, course):
        self.student = student
        self.course = course

class Satisfies:
    def __init__(self, course, program_requirement):
        self.course = course
        self.program_requirement = program_requirement

class ApprovedBy:
    def __init__(self, program_requirement, approval):
        self.program_requirement = program_requirement
        self.approval = approval

class Parser:
    def __init__(self, intermediate_representation):
        self.ir = intermediate_representation
        self.students = []
        self.courses = []
        self.requirements = []
        self.approvals = []
        
    def parse(self):
        try:
            for item in self.ir:
                if item['type'] == 'Student':
                    student = self.parse_student(item)
                    self.students.append(student)
                elif item['type'] == 'Course':
                    course = self.parse_course(item)
                    self.courses.append(course)
                elif item['type'] == 'ProgramRequirement':
                    requirement = self.parse_requirement(item)
                    self.requirements.append(requirement)
                elif item['type'] == 'Approval':
                    approval = self.parse_approval(item)
                    self.approvals.append(approval)
                elif item['type'] == 'Relation':
                    self.parse_relation(item)
        except KeyError as e:
            print(f"Key Error: The key {e} is missing in the IR item {item}")
        except Exception as e:
            print(f"Error: {e}")
    
    def parse_student(self, item):
        return Student(
            student_id=item['student_id'],
            name=item['name'],
            email=item['email'],
            degree_confer_date=item['degree_confer_date'],
            is_HCP=item['is_HCP'],
            is_Coterm=item['is_Coterm']
        )
    
    def parse_course(self, item):
        return Course(
            course_id=item['course_id'],
            title=item['title'],
            units=item['units'],
            grade=item['grade']
        )
    
    def parse_requirement(self, item):
        return ProgramRequirement(
            requirement_id=item['requirement_id'],
            description=item['description'],
            required_units=item['required_units']
        )
    
    def parse_approval(self, item):
        return Approval(
            approval_id=item['approval_id'],
            approved_by=item['approved_by'],
            approval_date=item['approval_date'],
            note=item['note']
        )
    
    def parse_relation(self, item):
        relation_type = item['relation_type']
        if relation_type == 'Enrolled_In':
            student = self.find_entity(self.students, 'student_id', item['student_id'])
            course = self.find_entity(self.courses, 'course_id', item['course_id'])
            if student and course:
                student.add_course(course)
        elif relation_type == 'Satisfies':
            course = self.find_entity(self.courses, 'course_id', item['course_id'])
            requirement = self.find_entity(self.requirements, 'requirement_id', item['requirement_id'])
            if course and requirement:
                course.add_requirement(requirement)
        elif relation_type == 'Approved_By':
            requirement = self.find_entity(self.requirements, 'requirement_id', item['requirement_id'])
            approval = self.find_entity(self.approvals, 'approval_id', item['approval_id'])
            if requirement and approval:
                requirement.add_approval(approval)
    
    def find_entity(self, entities, key, value):
        for entity in entities:
            if getattr(entity, key) == value:
                return entity
        return None

# Example Input Data (Intermediate Representation)
input_data = [
    {'type': 'Student', 'student_id': '05713381', 'name': 'Jeremy Lee Bregman', 'email': 'jeremy@stanford.edu', 'degree_confer_date': '01/08/2015', 'is_HCP': False, 'is_Coterm': True},
    {'type': 'Course', 'course_id': 'CS106A', 'title': 'Programming Methodology', 'units': 5, 'grade': 'B+'},
    # Add more student, course, requirement, approval, and relation items here as needed.
]

# Instantiate a parser with the input data and parse.
parser = Parser(input_data)
parser.parse()

# Debug: Print students and their courses for verification
for student in parser.students:
    print(f"Student: {student.name}")
for course in parser.courses:
    print(course.title)
    for course in student.courses:
        print(f"Course: {course.title}, Grade: {course.grade}")