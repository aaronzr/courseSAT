
from cvc5 import Solver, Kind, Term

solver = Solver()
solver.setLogic("QF_UF")  # Unquantified Formulas with Uninterpreted Functions

# Here we define our boolean variables for each thing's properties.
blue = {
    "Bob": solver.mkConst(solver.getBooleanSort(), "blue_Bob"),
    "Charlie": solver.mkConst(solver.getBooleanSort(), "blue_Charlie"),
    "Dave": solver.mkConst(solver.getBooleanSort(), "blue_Dave")
}
green = {
    "Dave": solver.mkConst(solver.getBooleanSort(), "green_Dave")
}
nice = {
    "Dave": solver.mkConst(solver.getBooleanSort(), "nice_Dave"),
    "Erin": solver.mkConst(solver.getBooleanSort(), "nice_Erin"),
    "Charlie": solver.mkConst(solver.getBooleanSort(), "nice_Charlie")
}
rough = {
    "Dave": solver.mkConst(solver.getBooleanSort(), "rough_Dave"),
    "Erin": solver.mkConst(solver.getBooleanSort(), "rough_Erin")
}
furry = {
    "Bob": solver.mkConst(solver.getBooleanSort(), "furry_Bob")
}
young = {
    "Erin": solver.mkConst(solver.getBooleanSort(), "young_Erin"),
    "Charlie": solver.mkConst(solver.getBooleanSort(), "young_Charlie"),
    "Dave": solver.mkConst(solver.getBooleanSort(), "young_Dave")
}
kind = {
    "Erin": solver.mkConst(solver.getBooleanSort(), "kind_Erin"),
    "Dave": solver.mkConst(solver.getBooleanSort(), "kind_Dave")
}

# Create a bound variable x for universal quantification
x = solver.mkVar(solver.getBooleanSort(), 'x')

# Create terms for applying each predicate to x
def apply_to_x(pred_dict, name):
    return solver.mkTerm(Kind.EQUAL, x, pred_dict[name])

blue_x = apply_to_x(blue, "Bob")
nice_x = apply_to_x(nice, "Dave")
kind_x = apply_to_x(kind, "Dave")
green_x = apply_to_x(green, "Dave")
furry_x = apply_to_x(furry, "Bob")
rough_x = apply_to_x(rough, "Dave")
young_x = apply_to_x(young, "Dave")

# Translating Statements
# 1. All blue, nice things are kind.
blue_nice_implies_kind = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, blue_x, nice_x), kind_x))

# 2. All furry, green things are blue.
furry_green_implies_blue = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, furry_x, green_x), blue_x))

# 3. Nice, rough things are blue.
nice_rough_implies_blue = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, nice_x, rough_x), blue_x))

# 4. If something is furry then it is rough.
furry_implies_rough = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, furry_x, rough_x))

# 5. All kind things are green.
kind_implies_green = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, kind_x, green_x))

# 6. Young things are nice.
young_implies_nice = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, young_x, nice_x))

# 7. All blue, rough things are furry.
blue_rough_implies_furry = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, blue_x, rough_x), furry_x))

# 8. Green, kind things are rough.
green_kind_implies_rough = solver.mkTerm(Kind.FORALL, 
    solver.mkTerm(Kind.VARIABLE_LIST, x), 
    solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, green_x, kind_x), rough_x))

# Assertions about objects
assertions = [
    blue["Bob"],
    furry["Bob"],
    blue["Charlie"],
    young["Charlie"],
    blue["Dave"],
    green["Dave"],
    nice["Dave"],
    rough["Dave"],
    young["Dave"],
    nice["Erin"],
    rough["Erin"]
]

# Test Statement: Erin is not kind
erin_not_kind = solver.mkTerm(Kind.NOT, kind["Erin"])

# Add assertions and formulas to the solver
formulas = [
    blue_nice_implies_kind,
    furry_green_implies_blue,
    nice_rough_implies_blue,
    furry_implies_rough,
    kind_implies_green,
    young_implies_nice,
    blue_rough_implies_furry,
    green_kind_implies_rough,
]

for assertion in assertions:
    solver.assertFormula(assertion)
for formula in formulas:
    solver.assertFormula(formula)

solver.assertFormula(erin_not_kind)

# Check if our scenario is satisfied
if solver.checkSat().isSat():
    print("The test statement is satisfied.")
else:
    print("The test statement is unsatisfied.")
