from typing import List, Dict, Union

class ASTNode:
    def __init__(self):
        self.children = []  # All nodes can have children.

class Student(ASTNode):
    def __init__(self, name, student_id, advisor, email, degree_confer_date, hcp, coterm):
        super().__init__()
        self.name = name
        self.student_id = student_id
        self.advisor = advisor
        self.email = email
        self.degree_confer_date = degree_confer_date
        self.hcp = hcp
        self.coterm = coterm

class Course(ASTNode):
    def __init__(self, course_number, title, units, grade):
        super().__init__()
        self.course_number = course_number
        self.title = title
        self.units = units
        self.grade = grade

class Requirement(ASTNode):
    def __init__(self, requirement_type, satisfied):
        super().__init__()
        self.requirement_type = requirement_type
        self.satisfied = satisfied
        self.subrequirements = []

class SubRequirement(ASTNode):
    def __init__(self, course, satisfied, waiver_allowed=False):
        super().__init__()
        self.course = course
        self.satisfied = satisfied
        self.waiver_allowed = waiver_allowed

class Relation(ASTNode):
    def __init__(self, relation_type, attributes):
        super().__init__()
        self.relation_type = relation_type
        self.attributes = attributes

class Constraint(ASTNode):
    def __init__(self, constraint_type, condition):
        super().__init__()
        self.constraint_type = constraint_type
        self.condition = condition


class Parser:
    def __init__(self, intermediate_representation):
        self.intermediate_representation = intermediate_representation
        self.ast = ASTNode()  # Root node

    def parse_student(self, student_data):
        student = Student(
            name=student_data['Name'],
            student_id=student_data['StudentID'],
            advisor=student_data['Advisor'],
            email=student_data['Email'],
            degree_confer_date=student_data['DegreeConferralDate'],
            hcp=student_data['HCP'],
            coterm=student_data['Coterm']
        )
        self.ast.children.append(student)
        return student

    def parse_courses(self, courses_data):
        courses = []
        for course_data in courses_data:
            course = Course(
                course_number=course_data['CourseNumber'],
                title=course_data['Title'],
                units=course_data['Units'],
                grade=course_data['Grade']
            )
            courses.append(course)
        return courses

    def parse_requirements(self, requirements_data):
        requirements = []
        for requirement_data in requirements_data:
            requirement = Requirement(
                requirement_type=requirement_data['RequirementType'],
                satisfied=requirement_data['Satisfied']
            )
            for subreq_data in requirement_data.get('SubRequirements', []):
                subreq = SubRequirement(
                    course=subreq_data['Course'],
                    satisfied=subreq_data['Satisfied'],
                    waiver_allowed=subreq_data.get('WaiverAllowed', False)
                )
                requirement.subrequirements.append(subreq)
            requirements.append(requirement)
        return requirements

    def parse_relations(self, relations_data):
        relations = []
        for relation_data in relations_data:
            relation = Relation(
                relation_type=relation_data['RelationType'],
                attributes=relation_data['Attributes']
            )
            relations.append(relation)
        return relations

    def parse_constraints(self, constraints_data):
        constraints = []
        for constraint_data in constraints_data:
            constraint = Constraint(
                constraint_type=constraint_data['ConstraintType'],
                condition=constraint_data['Condition']
            )
            constraints.append(constraint)
        return constraints

    def parse(self):
        ir = self.intermediate_representation

        student = self.parse_student(ir['Student'])
        courses = self.parse_courses(ir['Courses'])
        requirements = self.parse_requirements(ir['Requirements'])
        relations = self.parse_relations(ir['Relations'])
        constraints = self.parse_constraints(ir['Constraints'])

        student.children.extend(courses)
        student.children.extend(requirements)
        self.ast.children.extend(relations)
        self.ast.children.extend(constraints)

        return self.ast




# Example intermediate representation
intermediate_representation = {
    "Student": {
        "Name": "Alice Smith",
        "StudentID": "123456",
        "Advisor": "Dr. Bob",
        "Email": "alice@stanford.edu",
        "DegreeConferralDate": "2023-06-15",
        "HCP": True,
        "Coterm": False
    },
    "Courses": [
        {"CourseNumber": "CS103", "Title": "Logic, Automata", "Units": 3, "Grade": "A"},
        {"CourseNumber": "CS161", "Title": "Algorithmic Analysis", "Units": 4, "Grade": "B+"}
    ],
    "Requirements": [
        {
            "RequirementType": "Foundations",
            "Satisfied": False,
            "SubRequirements": [
                {"Course": "CS103", "Satisfied": True, "WaiverAllowed": False},
                {"Course": "Probability", "Satisfied": False, "WaiverAllowed": True}
            ]
        }
    ],
    "Relations": [
        {"RelationType": "Student-Takes-Course", "Attributes": {"Completed": True, "ForMS": True, "Waivers": []}}
    ],
    "Constraints": [
        {"ConstraintType": "General Constraints for MSCS Degree", "Condition": "TotalUnits >= 45"}
    ]
}

# Create a parser instance
parser = Parser(intermediate_representation)

# Parse to generate AST
ast = parser.parse()

# Print the AST structure
def print_ast(node, indent=""):
    print(indent + type(node).__name__)
    for child in node.children:
        print_ast(child, indent + "  ")

print_ast(ast)



from typing import List, Dict, Union

class ASTNode:
    def __init__(self):
        self.children = []  # All nodes can have children.

class Student(ASTNode):
    def __init__(self, name, student_id, advisor, email, degree_confer_date, hcp, coterm):
        super().__init__()
        self.name = name
        self.student_id = student_id
        self.advisor = advisor
        self.email = email
        self.degree_confer_date = degree_confer_date
        self.hcp = hcp
        self.coterm = coterm

class Course(ASTNode):
    def __init__(self, course_number, title, units, grade):
        super().__init__()
        self.course_number = course_number
        self.title = title
        self.units = units
        self.grade = grade

class Requirement(ASTNode):
    def __init__(self, requirement_type, satisfied):
        super().__init__()
        self.requirement_type = requirement_type
        self.satisfied = satisfied
        self.subrequirements = []

class SubRequirement(ASTNode):
    def __init__(self, course, satisfied, waiver_allowed=False):
        super().__init__()
        self.course = course
        self.satisfied = satisfied
        self.waiver_allowed = waiver_allowed

class Relation(ASTNode):
    def __init__(self, relation_type, attributes):
        super().__init__()
        self.relation_type = relation_type
        self.attributes = attributes

class Constraint(ASTNode):
    def __init__(self, constraint_type, condition):
        super().__init__()
        self.constraint_type = constraint_type
        self.condition = condition


class Parser:
    def __init__(self, intermediate_representation):
        self.intermediate_representation = intermediate_representation
        self.ast = ASTNode()  # Root node

    def parse_student(self, student_data):
        student = Student(
            name=student_data['Name'],
            student_id=student_data['StudentID'],
            advisor=student_data['Advisor'],
            email=student_data['Email'],
            degree_confer_date=student_data['DegreeConferralDate'],
            hcp=student_data['HCP'],
            coterm=student_data['Coterm']
        )
        self.ast.children.append(student)
        return student

    def parse_courses(self, courses_data):
        courses = []
        for course_data in courses_data:
            course = Course(
                course_number=course_data['CourseNumber'],
                title=course_data['Title'],
                units=course_data['Units'],
                grade=course_data['Grade']
            )
            courses.append(course)
        return courses

    def parse_requirements(self, requirements_data):
        requirements = []
        for requirement_data in requirements_data:
            requirement = Requirement(
                requirement_type=requirement_data['RequirementType'],
                satisfied=requirement_data['Satisfied']
            )
            for subreq_data in requirement_data.get('SubRequirements', []):
                subreq = SubRequirement(
                    course=subreq_data['Course'],
                    satisfied=subreq_data['Satisfied'],
                    waiver_allowed=subreq_data.get('WaiverAllowed', False)
                )
                requirement.subrequirements.append(subreq)
            requirements.append(requirement)
        return requirements

    def parse_relations(self, relations_data):
        relations = []
        for relation_data in relations_data:
            relation = Relation(
                relation_type=relation_data['RelationType'],
                attributes=relation_data['Attributes']
            )
            relations.append(relation)
        return relations

    def parse_constraints(self, constraints_data):
        constraints = []
        for constraint_data in constraints_data:
            constraint = Constraint(
                constraint_type=constraint_data['ConstraintType'],
                condition=constraint_data['Condition']
            )
            constraints.append(constraint)
        return constraints

    def parse(self):
        ir = self.intermediate_representation

        student = self.parse_student(ir['Student'])
        courses = self.parse_courses(ir['Courses'])
        requirements = self.parse_requirements(ir['Requirements'])
        relations = self.parse_relations(ir['Relations'])
        constraints = self.parse_constraints(ir['Constraints'])

        student.children.extend(courses)
        student.children.extend(requirements)
        self.ast.children.extend(relations)
        self.ast.children.extend(constraints)

        return self.ast

# Example intermediate representation
intermediate_representation = {
    "Student": {
        "Name": "Alice Smith",
        "StudentID": "123456",
        "Advisor": "Dr. Bob",
        "Email": "alice@stanford.edu",
        "DegreeConferralDate": "2023-06-15",
        "HCP": True,
        "Coterm": False
    },
    "Courses": [
        {"CourseNumber": "CS103", "Title": "Logic, Automata", "Units": 3, "Grade": "A"},
        {"CourseNumber": "CS161", "Title": "Algorithmic Analysis", "Units": 4, "Grade": "B+"}
    ],
    "Requirements": [
        {
            "RequirementType": "Foundations",
            "Satisfied": False,
            "SubRequirements": [
                {"Course": "CS103", "Satisfied": True, "WaiverAllowed": False},
                {"Course": "Probability", "Satisfied": False, "WaiverAllowed": True}
            ]
        }
    ],
    "Relations": [
        {"RelationType": "Student-Takes-Course", "Attributes": {"Completed": True, "ForMS": True, "Waivers": []}}
    ],
    "Constraints": [
        {"ConstraintType": "General Constraints for MSCS Degree", "Condition": "TotalUnits >= 45"}
    ]
}

# Create a parser instance
parser = Parser(intermediate_representation)

# Parse to generate AST
ast = parser.parse()

# Print the AST structure
def print_ast(node, indent=""):
    print(indent + type(node).__name__)
    for child in node.children:
        print_ast(child, indent + "  ")

print_ast(ast)