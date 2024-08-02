
import cvc5
from cvc5 import Solver

# Initialize solver
solver = Solver()

# Define technicians
technicians = ["stacy", "urma", "wim", "xena", "yolanda", "zane"]
repair_variables = ["radio", "television", "vcr"]

# Create repair predicates
repair_predicates = {
    technician: {machine: solver.mkConst(solver.getBooleanSort(), f"{technician}_{machine}") for machine in repair_variables}
    for technician in technicians
}

# Xena and exactly three other technicians repair radios
radios = [solver.mkTerm(cvc5.Kind.ITE, repair_predicates[t]["radio"], solver.mkInteger(1), solver.mkInteger(0)) for t in technicians]
solver.assertFormula(solver.mkTerm(cvc5.Kind.EQUAL, solver.mkTerm(cvc5.Kind.ADD, *radios), solver.mkInteger(4)))

# Yolanda repairs both televisions and VCRs
solver.assertFormula(repair_predicates["yolanda"]["television"])
solver.assertFormula(repair_predicates["yolanda"]["vcr"])

# Stacy does not repair any type of machine that Yolanda repairs
for machine in repair_variables:
    solver.assertFormula(solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, repair_predicates["stacy"][machine], repair_predicates["yolanda"][machine])))

# Zane repairs more types of machines than Yolanda
zane_repairs = [solver.mkTerm(cvc5.Kind.ITE, repair_predicates["zane"][machine], solver.mkInteger(1), solver.mkInteger(0)) for machine in repair_variables]
yolanda_repairs = [solver.mkTerm(cvc5.Kind.ITE, repair_predicates["yolanda"][machine], solver.mkInteger(1), solver.mkInteger(0)) for machine in repair_variables]

zane_count = solver.mkTerm(cvc5.Kind.ADD, *zane_repairs)
yolanda_count = solver.mkTerm(cvc5.Kind.ADD, *yolanda_repairs)
solver.assertFormula(solver.mkTerm(cvc5.Kind.GT, zane_count, yolanda_count))

# Wim does not repair any type of machine that Stacy repairs
for machine in repair_variables:
    solver.assertFormula(solver.mkTerm(cvc5.Kind.NOT, solver.mkTerm(cvc5.Kind.AND, repair_predicates["wim"][machine], repair_predicates["stacy"][machine])))

# Urma repairs exactly two types of machines
urma_repairs = [solver.mkTerm(cvc5.Kind.ITE, repair_predicates["urma"][machine], solver.mkInteger(1), solver.mkInteger(0)) for machine in repair_variables]
urma_count = solver.mkTerm(cvc5.Kind.ADD, *urma_repairs)
solver.assertFormula(solver.mkTerm(cvc5.Kind.EQUAL, urma_count, solver.mkInteger(2)))

# Define pair check conditions
def check_pair(tech1, tech2):
    return solver.mkTerm(cvc5.Kind.AND, *[
        solver.mkTerm(cvc5.Kind.EQUAL, repair_predicates[tech1][machine], repair_predicates[tech2][machine])
        for machine in repair_variables
    ])

# Define the choices
choices = {
    "A": ("stacy", "urma"),
    "B": ("urma", "yolanda"),
    "C": ("urma", "xena"),
    "D": ("wim", "xena"),
    "E": ("xena", "yolanda"),
}

# Check each choice
for choice, (tech1, tech2) in choices.items():
    result = solver.checkSatAssuming(check_pair(tech1, tech2))
    print(f"Choice {choice}: {tech1} and {tech2} - {result}")
