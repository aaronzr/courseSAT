
import cvc5

# Create SMT solver instance
solver = cvc5.Solver()

# Set the logic
solver.setLogic("QF_UF")

# Define sorts for entities and predicates
Entity = solver.mkUninterpretedSort("Entity")
Predicate = solver.mkFunctionSort([Entity], solver.getBooleanSort())

# Define entities
baldEagle = solver.mkConst(Entity, "baldEagle")
cat = solver.mkConst(Entity, "cat")
lion = solver.mkConst(Entity, "lion")
rabbit = solver.mkConst(Entity, "rabbit")

# Define predicates
isNice = solver.mkConst(Predicate, "isNice")
isRed = solver.mkConst(Predicate, "isRed")
isGreen = solver.mkConst(Predicate, "isGreen")
isKind = solver.mkConst(Predicate, "isKind")
isYoung = solver.mkConst(Predicate, "isYoung")
eats = solver.mkConst(solver.mkFunctionSort([Entity, Entity], solver.getBooleanSort()), "eats")
likes = solver.mkConst(solver.mkFunctionSort([Entity, Entity], solver.getBooleanSort()), "likes")
needs = solver.mkConst(solver.mkFunctionSort([Entity, Entity], solver.getBooleanSort()), "needs")

# Contextual Statements
# 1. If someone is nice and they eat the cat then they eat the lion.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.AND,
            solver.mkTerm(cvc5.Kind.APPLY_UF, isNice, baldEagle),
            solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, cat)
        ),
        solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, lion)
    )
)

# 2. If someone is red then they eat the lion.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.APPLY_UF, isRed, baldEagle),
        solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, lion)
    )
)

# 3. If someone eats the lion then the lion eats the cat.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, lion),
        solver.mkTerm(cvc5.Kind.APPLY_UF, eats, lion, cat)
    )
)

# 4. If someone is nice and they need the rabbit then the rabbit does not need the lion.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.AND,
            solver.mkTerm(cvc5.Kind.APPLY_UF, isNice, baldEagle),
            solver.mkTerm(cvc5.Kind.APPLY_UF, needs, baldEagle, rabbit)
        ),
        solver.mkTerm(cvc5.Kind.NOT,
            solver.mkTerm(cvc5.Kind.APPLY_UF, needs, rabbit, lion)
        )
    )
)

# 5. If someone eats the cat then they are red.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, cat),
        solver.mkTerm(cvc5.Kind.APPLY_UF, isRed, baldEagle)
    )
)

# 6. If someone is young and they like the lion then they do not need the rabbit.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.AND,
            solver.mkTerm(cvc5.Kind.APPLY_UF, isYoung, baldEagle),
            solver.mkTerm(cvc5.Kind.APPLY_UF, likes, baldEagle, lion)
        ),
        solver.mkTerm(cvc5.Kind.NOT,
            solver.mkTerm(cvc5.Kind.APPLY_UF, needs, baldEagle, rabbit)
        )
    )
)

# 7. If the bald eagle needs the cat and the cat does not eat the lion then the cat likes the rabbit.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.IMPLIES,
        solver.mkTerm(cvc5.Kind.AND,
            solver.mkTerm(cvc5.Kind.APPLY_UF, needs, baldEagle, cat),
            solver.mkTerm(cvc5.Kind.NOT,
                solver.mkTerm(cvc5.Kind.APPLY_UF, eats, cat, lion)
            )
        ),
        solver.mkTerm(cvc5.Kind.APPLY_UF, likes, cat, rabbit)
    )
)

# 8. The bald eagle eats the cat.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, cat))

# 9. The bald eagle eats the rabbit.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, rabbit))

# 10. The bald eagle is kind.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, isKind, baldEagle))

# 11. The bald eagle likes the lion.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, likes, baldEagle, lion))

# 12. The bald eagle likes the rabbit.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, likes, baldEagle, rabbit))

# 13. The bald eagle needs the cat.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, needs, baldEagle, cat))

# 14. The bald eagle needs the lion.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, needs, baldEagle, lion))

# 15. The cat eats the bald eagle.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, eats, cat, baldEagle))

# 16. The cat is not green.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.NOT,
        solver.mkTerm(cvc5.Kind.APPLY_UF, isGreen, cat)
    )
)

# 17. The lion does not eat the rabbit.
solver.assertFormula(
    solver.mkTerm(cvc5.Kind.NOT,
        solver.mkTerm(cvc5.Kind.APPLY_UF, eats, lion, rabbit)
    )
)

# 18. The lion needs the bald eagle.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, needs, lion, baldEagle))

# 19. The rabbit eats the bald eagle.
solver.assertFormula(solver.mkTerm(cvc5.Kind.APPLY_UF, eats, rabbit, baldEagle))

# Test Statement
# The bald eagle does not eat the lion.
test_statement = solver.mkTerm(cvc5.Kind.NOT, 
                               solver.mkTerm(cvc5.Kind.APPLY_UF, eats, baldEagle, lion))

# Check satisfiability of the test statement
solver.push()  # Save the current state of the solver
solver.assertFormula(test_statement)
result = solver.checkSat()
solver.pop()  # Restore the state of the solver

if result.isSat():
    print("The test statement is unsatisfied (i.e., The bald eagle eats the lion).")
else:
    print("The test statement is satisfied (i.e., The bald eagle does not eat the lion).")

# Check the overall consistency of the formulas
result = solver.checkSat()
if result.isSat():
    print("The overall set of statements is consistent.")
else:
    print("The overall set of statements is inconsistent.")
