
import cvc5

solver = cvc5.Solver()

# Define students visiting cities as integers
Hubert = solver.mkConst(solver.getIntegerSort(), "Hubert")
Lori = solver.mkConst(solver.getIntegerSort(), "Lori")
Paul = solver.mkConst(solver.getIntegerSort(), "Paul")
Regina = solver.mkConst(solver.getIntegerSort(), "Regina")
Sharon = solver.mkConst(solver.getIntegerSort(), "Sharon")

# State the cities as constants
montreal = solver.mkInteger(1)
toronto = solver.mkInteger(2)
vancouver = solver.mkInteger(3)

students = [Hubert, Lori, Paul, Regina, Sharon]

# Each student visits exactly one of the cities {1, 2, 3}
for student in students:
    solver.assertFormula(
        solver.mkTerm(cvc5.Kind.OR,
                      solver.mkTerm(cvc5.Kind.EQUAL, student, montreal),
                      solver.mkTerm(cvc5.Kind.EQUAL, student, toronto),
                      solver.mkTerm(cvc5.Kind.EQUAL, student, vancouver))
    )

# Translate the conditions
# a. Sharon visits a different city than Paul
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.NOT,
                  solver.mkTerm(cvc5.Kind.EQUAL, Sharon, Paul))
)

# b. Hubert visits the same city as Regina
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.EQUAL, Hubert, Regina)
)

# c. Lori visits Montreal or else Toronto
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.OR,
                  solver.mkTerm(cvc5.Kind.EQUAL, Lori, montreal),
                  solver.mkTerm(cvc5.Kind.EQUAL, Lori, toronto))
)

# d. If Paul visits Vancouver, Hubert visits Vancouver with him
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
                  solver.mkTerm(cvc5.Kind.EQUAL, Paul, vancouver),
                  solver.mkTerm(cvc5.Kind.EQUAL, Hubert, vancouver))
)

# e. Each student visits one of the cities with at least one of the other four students
def at_least_two_students(city):
    return solver.mkTerm(cvc5.Kind.OR,
                         solver.mkTerm(cvc5.Kind.EQUAL, Hubert, city),
                         solver.mkTerm(cvc5.Kind.EQUAL, Lori, city),
                         solver.mkTerm(cvc5.Kind.EQUAL, Paul, city),
                         solver.mkTerm(cvc5.Kind.EQUAL, Regina, city),
                         solver.mkTerm(cvc5.Kind.EQUAL, Sharon, city))

for student in students:
    solver.assertFormula(
        solver.mkTerm(cvc5.Kind.OR,
                      at_least_two_students(montreal),
                      at_least_two_students(toronto),
                      at_least_two_students(vancouver))
    )

# Evaluate Choices
choices = {
    "A": solver.mkTerm(cvc5.Kind.IMPLIES,
                       solver.mkTerm(cvc5.Kind.OR,
                                     solver.mkTerm(cvc5.Kind.EQUAL, Hubert, montreal),
                                     solver.mkTerm(cvc5.Kind.EQUAL, Lori, montreal),
                                     solver.mkTerm(cvc5.Kind.EQUAL, Paul, montreal),
                                     solver.mkTerm(cvc5.Kind.EQUAL, Regina, montreal),
                                     solver.mkTerm(cvc5.Kind.EQUAL, Sharon, montreal)),
                       solver.mkTerm(cvc5.Kind.EQUAL, Lori, montreal))}

for choice, formula in choices.items():
    solver.assertFormula(formula)
    if solver.checkSat().isSat():
        print(f"Choice ({choice}) is satisfied")
    else:
        print(f"Choice ({choice}) is not satisfied")
    solver.resetAssertions()  # reset constraints for next choice

# Repeat similar blocks for other choices B, C, D, E while preserving correct logic.
