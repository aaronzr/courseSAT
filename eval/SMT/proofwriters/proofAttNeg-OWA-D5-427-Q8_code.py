
import cvc5
from cvc5 import Kind

# Create the solver
s = cvc5.Solver()

# Defining sorts
BoolSort = s.getBooleanSort()

# Define individuals
Anne = s.mkConst(BoolSort, 'Anne')
Charlie = s.mkConst(BoolSort, 'Charlie')
Gary = s.mkConst(BoolSort, 'Gary')
Harry = s.mkConst(BoolSort, 'Harry')

# Define predicates for characteristics using function declarations
white = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "white")
blue = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "blue")
furry = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "furry")
round = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "round")
green = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "green")
rough = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "rough")
nice = s.mkConst(s.mkFunctionSort([BoolSort], BoolSort), "nice")

# Define variable for universal quantification
x = s.mkVar(BoolSort, 'x')

# Helper function to create quantified statements
def forall(vars, body):
    bound_var_list = s.mkTerm(Kind.VARIABLE_LIST, *vars)
    return s.mkTerm(Kind.FORALL, bound_var_list, body)

# Translating contextual statements into cvc5 formulas

# 1. "If something is white then it is blue."
stmt1 = forall([x], s.mkTerm(Kind.IMPLIES, s.mkTerm(Kind.APPLY_UF, white, x), s.mkTerm(Kind.APPLY_UF, blue, x)))
s.assertFormula(stmt1)

# 2. "All furry things are round."
stmt2 = forall([x], s.mkTerm(Kind.IMPLIES, s.mkTerm(Kind.APPLY_UF, furry, x), s.mkTerm(Kind.APPLY_UF, round, x)))
s.assertFormula(stmt2)

# 3. "Green, rough things are round."
stmt3 = forall([x], s.mkTerm(Kind.IMPLIES, s.mkTerm(Kind.AND, s.mkTerm(Kind.APPLY_UF, green, x), s.mkTerm(Kind.APPLY_UF, rough, x)), s.mkTerm(Kind.APPLY_UF, round, x)))
s.assertFormula(stmt3)

# 4. "Blue things are furry."
stmt4 = forall([x], s.mkTerm(Kind.IMPLIES, s.mkTerm(Kind.APPLY_UF, blue, x), s.mkTerm(Kind.APPLY_UF, furry, x)))
s.assertFormula(stmt4)

# 5. "If Charlie is furry then Charlie is nice."
stmt5 = s.mkTerm(Kind.IMPLIES, s.mkTerm(Kind.APPLY_UF, furry, Charlie), s.mkTerm(Kind.APPLY_UF, nice, Charlie))
s.assertFormula(stmt5)

# 6. "Rough, round things are white."
stmt6 = forall([x], s.mkTerm(Kind.IMPLIES, s.mkTerm(Kind.AND, s.mkTerm(Kind.APPLY_UF, rough, x), s.mkTerm(Kind.APPLY_UF, round, x)), s.mkTerm(Kind.APPLY_UF, white, x)))
s.assertFormula(stmt6)

# 7, 8, 9. "Anne is furry.", "Anne is not green.", "Anne is white."
stmt7 = s.mkTerm(Kind.APPLY_UF, furry, Anne)
stmt8 = s.mkTerm(Kind.NOT, s.mkTerm(Kind.APPLY_UF, green, Anne))
stmt9 = s.mkTerm(Kind.APPLY_UF, white, Anne)
s.assertFormula(stmt7)
s.assertFormula(stmt8)
s.assertFormula(stmt9)

# 10, 11. "Charlie is green.", "Charlie is rough."
stmt10 = s.mkTerm(Kind.APPLY_UF, green, Charlie)
stmt11 = s.mkTerm(Kind.APPLY_UF, rough, Charlie)
s.assertFormula(stmt10)
s.assertFormula(stmt11)

# 12, 13, 14, 15, 16, 17. "Gary is blue.", "Gary is furry.", "Gary is green.", "Gary is nice.", "Gary is round.", "Gary is white."
stmt12 = s.mkTerm(Kind.APPLY_UF, blue, Gary)
stmt13 = s.mkTerm(Kind.APPLY_UF, furry, Gary)
stmt14 = s.mkTerm(Kind.APPLY_UF, green, Gary)
stmt15 = s.mkTerm(Kind.APPLY_UF, nice, Gary)
stmt16 = s.mkTerm(Kind.APPLY_UF, round, Gary)
stmt17 = s.mkTerm(Kind.APPLY_UF, white, Gary)
s.assertFormula(stmt12)
s.assertFormula(stmt13)
s.assertFormula(stmt14)
s.assertFormula(stmt15)
s.assertFormula(stmt16)
s.assertFormula(stmt17)

# 18, 19, 20. "Harry is nice.", "Harry is rough.", "Harry is round."
stmt18 = s.mkTerm(Kind.APPLY_UF, nice, Harry)
stmt19 = s.mkTerm(Kind.APPLY_UF, rough, Harry)
stmt20 = s.mkTerm(Kind.APPLY_UF, round, Harry)
s.assertFormula(stmt18)
s.assertFormula(stmt19)
s.assertFormula(stmt20)

# Translating the test statement "Charlie is not blue."
test_stmt = s.mkTerm(Kind.NOT, s.mkTerm(Kind.APPLY_UF, blue, Charlie))

# Testing the logic
s.assertFormula(test_stmt)
result = s.checkSat()
print(result)
