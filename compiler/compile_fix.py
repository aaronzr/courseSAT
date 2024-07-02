from cvc5 import Solver, Kind
from parse_fix import *

class CVC5Compiler:
    def __init__(self, ast):
        self.ast = ast
        self.solver = Solver()
        self.solver.setOption("produce-models", "true")
        self.solver.setOption("produce-unsat-cores", "true")
        self.solver.setLogic("ALL")
        self.variables = {}

    def compile(self):
        for constraint in self.ast.children:
            if isinstance(constraint, Constraint):
                self.compile_constraint(constraint)

    def compile_constraint(self, constraint):
        if constraint.constraint_type == "General Constraints for MSCS Degree":
            condition = constraint.condition
            if condition == "TotalUnits >= 45":
                total_units = self.compute_total_units()
                formula = self.solver.mkTerm(Kind.GEQ, total_units, self.solver.mkInteger(45))
                self.solver.assertFormula(formula)
    
    def compute_total_units(self):
        student_node = self.ast.children[0]
        total_units = self.solver.mkInteger(0)
        for course in student_node.children:
            if isinstance(course, Course):
                total_units = self.solver.mkTerm(Kind.ADD, total_units, self.solver.mkInteger(course.units))
        return total_units

    def check_sat(self):
        return self.solver.checkSat()

    def check_core(self):
        return self.solver.getUnsatCore()

# Instantiate the compiler with the AST
compiler = CVC5Compiler(ast)
compiler.compile()

# Check satisfiability
result = compiler.check_sat()
print(result)
print("unsatisfied core is: ", compiler.check_core())
  