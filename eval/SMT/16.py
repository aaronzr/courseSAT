
import cvc5
from cvc5 import Kind

solver = cvc5.Solver()

# Create sorts
Expert = solver.mkUninterpretedSort("Expert")
Language = solver.mkUninterpretedSort("Language")

# Expert constants
lawyer = solver.mkConst(Expert, 'lawyer')
naturalist = solver.mkConst(Expert, 'naturalist')
oceanographer = solver.mkConst(Expert, 'oceanographer')
physicist = solver.mkConst(Expert, 'physicist')
statistician = solver.mkConst(Expert, 'statistician')

# Language constants
French = solver.mkConst(Language, 'French')
Hindi = solver.mkConst(Language, 'Hindi')
Japanese = solver.mkConst(Language, 'Japanese')
Mandarin = solver.mkConst(Language, 'Mandarin')

# Presentation sequence as variables
P = [solver.mkConst(Expert, f'P{i+1}') for i in range(5)]

# Define the function to pair experts with languages
expert_var = solver.mkVar(Expert, "expert")
language_of_expert = solver.defineFun("language_of_expert", [expert_var], Language, solver.mkConst(Language, "const"))

# Constraints
constraints = []

# Each presentation should be given by a unique expert
constraints.append(solver.mkTerm(Kind.DISTINCT, *P))

# Each expert speaks exactly one language
all_experts = [lawyer, naturalist, oceanographer, physicist, statistician]
all_languages = [French, Hindi, Japanese, Mandarin]

for expert in all_experts:
    or_terms = [solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, expert), lang) for lang in all_languages]
    constraints.append(solver.mkTerm(Kind.OR, *or_terms))

# Each presentation is assigned to one of the experts
for i in range(5):
    constraints.append(solver.mkTerm(Kind.OR, *[solver.mkTerm(Kind.EQUAL, P[i], expert) for expert in all_experts]))

# Language constraints for presentation order
constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, P[1]), Hindi))
constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, P[0]), Japanese))
constraints.append(solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, P[4]), Japanese))

# Specific expert language constraints
constraints.append(
    solver.mkTerm(
        Kind.OR,
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, lawyer), Mandarin),
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, lawyer), French)
    )
)

constraints.append(
    solver.mkTerm(
        Kind.OR,
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, P[2]), French),
        solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, P[2]), Japanese)
    )
)

# Physicist and oceanographer constraints
constraints.append(solver.mkTerm(
    Kind.OR,
    solver.mkTerm(Kind.EQUAL, P[2], physicist),
    solver.mkTerm(Kind.EQUAL, P[2], oceanographer)
))
constraints.append(solver.mkTerm(
    Kind.OR,
    solver.mkTerm(Kind.EQUAL, P[3], physicist),
    solver.mkTerm(Kind.EQUAL, P[3], oceanographer)
))

# Two presentations in the same language constraint
for lang in all_languages:
    language_count = [solver.mkTerm(Kind.EQUAL, solver.mkTerm(Kind.APPLY_UF, language_of_expert, P[i]), lang) for i in range(5)]
    for i in range(len(language_count)):
        for j in range(i + 1, len(language_count)):
            constraints.append(solver.mkTerm(Kind.OR, solver.mkTerm(Kind.NOT, language_count[i]), solver.mkTerm(Kind.NOT, language_count[j])))

# Adding constraints to the solver
for constraint in constraints:
    solver.assertFormula(constraint)

# Question check: Could the order be among the given choices?
def check_order(order):
    new_solver = cvc5.Solver()
    
    # Duplicate the existing sorts
    Expert_new = new_solver.mkUninterpretedSort("Expert")
    Language_new = new_solver.mkUninterpretedSort("Language")

    # Define the function again in new_solver context
    expert_var = new_solver.mkVar(Expert_new, "expert")
    language_of_expert = new_solver.defineFun("language_of_expert", [expert_var], Language_new, new_solver.mkConst(Language_new, "const"))

    # Variables for presentations
    P_new = [new_solver.mkConst(Expert_new, f'P{i+1}') for i in range(5)]

    # Reconstruct all experts
    lawyer_new = new_solver.mkConst(Expert_new, 'lawyer')
    naturalist_new = new_solver.mkConst(Expert_new, 'naturalist')
    oceanographer_new = new_solver.mkConst(Expert_new, 'oceanographer')
    physicist_new = new_solver.mkConst(Expert_new, 'physicist')
    statistician_new = new_solver.mkConst(Expert_new, 'statistician')

    # List references
    all_experts_new = [lawyer_new, naturalist_new, oceanographer_new, physicist_new, statistician_new]

    # Reconstruct all languages
    French_new = new_solver.mkConst(Language_new, 'French')
    Hindi_new = new_solver.mkConst(Language_new, 'Hindi')
    Japanese_new = new_solver.mkConst(Language_new, 'Japanese')
    Mandarin_new = new_solver.mkConst(Language_new, 'Mandarin')

    # List references
    all_languages_new = [French_new, Hindi_new, Japanese_new, Mandarin_new]

    # Function constraints
    for expert_new in all_experts_new:
        or_terms = [new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, expert_new), lang_new) for lang_new in all_languages_new]
        new_solver.assertFormula(new_solver.mkTerm(Kind.OR, *or_terms))

    # Presentation assignment constraints
    for i in range(5):
        new_solver.assertFormula(new_solver.mkTerm(Kind.OR, *[new_solver.mkTerm(Kind.EQUAL, P_new[i], expert_new) for expert_new in all_experts_new]))

    # Language constraints for presentation order
    new_solver.assertFormula(new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, P_new[1]), Hindi_new))
    new_solver.assertFormula(new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, P_new[0]), Japanese_new))
    new_solver.assertFormula(new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, P_new[4]), Japanese_new))

    # Specific expert language constraints
    new_solver.assertFormula(new_solver.mkTerm(
        Kind.OR,
        new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, lawyer_new), Mandarin_new),
        new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, lawyer_new), French_new)
    ))
    
    new_solver.assertFormula(new_solver.mkTerm(
        Kind.OR,
        new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, P_new[2]), French_new),
        new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, P_new[2]), Japanese_new)
    ))

    # Physicist and oceanographer constraints
    new_solver.assertFormula(new_solver.mkTerm(
        Kind.OR,
        new_solver.mkTerm(Kind.EQUAL, P_new[2], physicist_new),
        new_solver.mkTerm(Kind.EQUAL, P_new[2], oceanographer_new)
    ))
    new_solver.assertFormula(new_solver.mkTerm(
        Kind.OR,
        new_solver.mkTerm(Kind.EQUAL, P_new[3], physicist_new),
        new_solver.mkTerm(Kind.EQUAL, P_new[3], oceanographer_new)
    ))

    # Two presentations in the same language constraints
    for lang_new in all_languages_new:
        language_count = [new_solver.mkTerm(Kind.EQUAL, new_solver.mkTerm(Kind.APPLY_UF, language_of_expert, P_new[i]), lang_new) for i in range(5)]
        for i in range(len(language_count)):
            for j in range(i + 1, len(language_count)):
                new_solver.assertFormula(new_solver.mkTerm(Kind.OR, new_solver.mkTerm(Kind.NOT, language_count[i]), new_solver.mkTerm(Kind.NOT, language_count[j])))

    # Check the specific order
    # Note the mapping: order now needs to consist of new_solver's experts, not the original ones
    order_mapping = [all_experts_new[all_experts.index(o)] for o in order]
    new_constraints = [new_solver.mkTerm(Kind.EQUAL, P_new[i], order_mapping[i]) for i in range(5)]
    for constraint in new_constraints:
        new_solver.assertFormula(constraint)

    return new_solver.checkSat().isSat()

# Choices
choices = [
    [physicist, statistician, lawyer, naturalist, oceanographer],
    [physicist, naturalist, oceanographer, lawyer, statistician],
    [oceanographer, statistician, naturalist, lawyer, physicist],
    [oceanographer, statistician, lawyer, naturalist, physicist]
]

# Evaluate choices
for idx, choice in enumerate(choices):
    if check_order(choice):
        print(f'Choice {chr(65+idx)} could be the order.')
    else:
        print(f'Choice {chr(65+idx)} cannot be the order.')
