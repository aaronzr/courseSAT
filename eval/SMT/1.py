
import cvc5
from cvc5 import Kind

# Initialize the CVC5 solver
solver = cvc5.Solver()

# Set the logic explicitly (optional but can be useful for certain features)
solver.setLogic("ALL")

# Create enumeration sorts for experts and languages
Expert = solver.mkDatatypeDecl("Expert")
Lawyer = solver.mkDatatypeConstructorDecl("Lawyer")
Naturalist = solver.mkDatatypeConstructorDecl("Naturalist")
Oceanographer = solver.mkDatatypeConstructorDecl("Oceanographer")
Physicist = solver.mkDatatypeConstructorDecl("Physicist")
Statistician = solver.mkDatatypeConstructorDecl("Statistician")
Expert.addConstructor(Lawyer)
Expert.addConstructor(Naturalist)
Expert.addConstructor(Oceanographer)
Expert.addConstructor(Physicist)
Expert.addConstructor(Statistician)
Experts = solver.mkDatatypeSort(Expert)

Language = solver.mkDatatypeDecl("Language")
French = solver.mkDatatypeConstructorDecl("French")
Hindi = solver.mkDatatypeConstructorDecl("Hindi")
Japanese = solver.mkDatatypeConstructorDecl("Japanese")
Mandarin = solver.mkDatatypeConstructorDecl("Mandarin")
Language.addConstructor(French)
Language.addConstructor(Hindi)
Language.addConstructor(Japanese)
Language.addConstructor(Mandarin)
Languages = solver.mkDatatypeSort(Language)

# Extract constructors from datatype sorts
statisticianConstructor = Experts.getDatatype().getConstructor("Statistician")
lawyerConstructor = Experts.getDatatype().getConstructor("Lawyer")
naturalistConstructor = Experts.getDatatype().getConstructor("Naturalist")
oceanographerConstructor = Experts.getDatatype().getConstructor("Oceanographer")
physicistConstructor = Experts.getDatatype().getConstructor("Physicist")

frenchConstructor = Languages.getDatatype().getConstructor("French")
hindiConstructor = Languages.getDatatype().getConstructor("Hindi")
japaneseConstructor = Languages.getDatatype().getConstructor("Japanese")
mandarinConstructor = Languages.getDatatype().getConstructor("Mandarin")

# Create terms for each constructor using the operator term
StatisticianTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, statisticianConstructor.getTerm())
LawyerTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, lawyerConstructor.getTerm())
NaturalistTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, naturalistConstructor.getTerm())
OceanographerTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, oceanographerConstructor.getTerm())
PhysicistTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, physicistConstructor.getTerm())

FrenchTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, frenchConstructor.getTerm())
HindiTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, hindiConstructor.getTerm())
JapaneseTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, japaneseConstructor.getTerm())
MandarinTerm = solver.mkTerm(Kind.APPLY_CONSTRUCTOR, mandarinConstructor.getTerm())

# Declarations for experts and languages in each presentation
E = [solver.mkConst(Experts, f"E{i+1}") for i in range(5)]
L = [solver.mkConst(Languages, f"L{i+1}") for i in range(5)]

# Constraints based on the provided problem

# 1. Exactly two of the presentations are in the same language.
solver.assertFormula(solver.mkTerm(Kind.DISTINCT, *L))  # All presentations have distinct languages initially

two_same_language = [
    solver.mkTerm(Kind.EQUAL, L[i], L[j]) for i in range(4) for j in range(i+1, 5)
]
exists_condition = solver.mkTerm(Kind.OR, *two_same_language)

# Create a Boolean variable for each pair of equal languages
bool_vars = [solver.mkConst(solver.getBooleanSort(), f"pair_{i}_{j}") for i in range(4) for j in range(i+1, 5)]

# Constraint ensuring exactly two matching pairs
conditions_with_bools = [
    solver.mkTerm(Kind.EQUAL, bool_var, condition)
    for bool_var, condition in zip(bool_vars, two_same_language)
]

# Convert boolean variables to 1 if true, else 0, and sum them
sum_bools = solver.mkTerm(
    Kind.ADD,
    *[solver.mkTerm(Kind.ITE, bool_var, solver.mkInteger(1), solver.mkInteger(0)) for bool_var in bool_vars]
)

number_of_true_bools = solver.mkTerm(Kind.EQUAL, sum_bools, solver.mkInteger(2))

solver.assertFormula(solver.mkTerm(Kind.AND, *conditions_with_bools))
solver.assertFormula(number_of_true_bools)

# 2. The statistician gives the second presentation in Hindi.
solver.assertFormula(solver.mkTerm(Kind.EQUAL, E[1], StatisticianTerm))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, L[1], HindiTerm))

# 3. The lawyer gives the fourth presentation in either Mandarin or French.
solver.assertFormula(solver.mkTerm(Kind.EQUAL, E[3], LawyerTerm))
solver.assertFormula(solver.mkTerm(
    Kind.OR,
    solver.mkTerm(Kind.EQUAL, L[3], MandarinTerm),
    solver.mkTerm(Kind.EQUAL, L[3], FrenchTerm)
))

# 4. The oceanographer presents in either French or Japanese; the same is true of the physicist.
oceanographer_presentations = solver.mkTerm(
    Kind.OR,
    solver.mkTerm(Kind.EQUAL, L[2], FrenchTerm),  # Corrected index from 'L[3]' to 'L[2]'
    solver.mkTerm(Kind.EQUAL, L[2], JapaneseTerm) # Corrected index from 'L[3]' to 'L[2]'
)

physicist_presentations = solver.mkTerm(
    Kind.OR,
    solver.mkTerm(Kind.EQUAL, L[4], FrenchTerm),
    solver.mkTerm(Kind.EQUAL, L[4], JapaneseTerm)
)

solver.assertFormula(solver.mkTerm(Kind.AND, oceanographer_presentations, physicist_presentations))

# 5. The first presentation and the last presentation are in Japanese.
solver.assertFormula(solver.mkTerm(Kind.EQUAL, L[0], JapaneseTerm))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, L[4], JapaneseTerm))

# Options to be checked
options = [
    {"order": [PhysicistTerm, StatisticianTerm, LawyerTerm, NaturalistTerm, OceanographerTerm], "name": "Option A"},
    {"order": [PhysicistTerm, NaturalistTerm, OceanographerTerm, LawyerTerm, StatisticianTerm], "name": "Option B"},
    {"order": [OceanographerTerm, StatisticianTerm, NaturalistTerm, LawyerTerm, PhysicistTerm], "name": "Option C"},
    {"order": [OceanographerTerm, StatisticianTerm, LawyerTerm, NaturalistTerm, PhysicistTerm], "name": "Option D"},
]

# Evaluate each option
for option in options:
    solver.push()  # Save the current state
    for i in range(5):
        solver.assertFormula(solver.mkTerm(Kind.EQUAL, E[i], option["order"][i]))
    
    # Check satisfiability
    satisfiable = solver.checkSat().isSat()
    
    # Output result
    print(f"{option['name']}: {'Satisfied' if satisfiable else 'Unsatisfied'}")
    
    solver.pop()  # Restore the previous state
