To tackle the given task, we'll first translate each sentence in the list of contextual statements into a form suitable for CVC5 SMT solver in Python. This translation involves recognizing the parameters and logical structure of each sentence. Let's proceed step by step:

1. **Rough, green things are nice.**
2. **If something is blue and round then it is nice.**
3. **Nice, rough things are blue.**
4. **If something is green then it is round.**
5. **Cold, smart things are rough.**
6. **All round things are cold.**
7. **Bob is blue.**
8. **Charlie is green.**
9. **Charlie is smart.**
10. **Erin is rough.**
11. **Erin is smart.**
12. **Fiona is rough.**
13. **Fiona is smart.**
14. **Charlie is not blue.**

Let's begin writing each statement in CVC5's SMT format using Python. Below is the code which accomplishes this:

```python
import cvc5
from cvc5 import Kind

# Create an instance of the solver
solver = cvc5.Solver()

# Declare the sorts
Person = solver.getUninterpretedSort("Person")

# Declare the predicates
Rough = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))
Green = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))
Nice = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))
Blue = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))
Round = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))
Cold = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))
Smart = solver.mkPredicate(Person, solver.mkUninterpretedSort("Bool"))

# Declare the individuals
Bob = solver.mkConst(Person, "Bob")
Charlie = solver.mkConst(Person, "Charlie")
Erin = solver.mkConst(Person, "Erin")
Fiona = solver.mkConst(Person, "Fiona")

# Adding the constraints
# Rough and Green things are Nice
solver.assertFormula(solver.mkForall(solver.mkVar(Person, "x"),
    solver.mkTerm(Kind.And, Rough(solver.mkVar(Person, "x")), Green(solver.mkVar(Person, "x")),
    Nice(solver.mkVar(Person, "x")))))

# If something is Blue and Round then it is Nice
solver.assertFormula(solver.mkForall(solver.mkVar(Person, "x"),
    solver.mkTerm(Kind.Implies, solver.mkTerm(Kind.And, Blue(solver.mkVar(Person, "x")), Round(solver.mkVar(Person, "x"))),
    Nice(solver.mkVar(Person, "x")))))

# Nice and Rough things are Blue
solver.assertFormula(solver.mkForall(solver.mkVar(Person, "x"),
    solver.mkTerm(Kind.And, Nice(solver.mkVar(Person, "x")), Rough(solver.mkVar(Person, "x")),
    Blue(solver.mkVar(Person, "x")))))

# If something is Green then it is Round
solver.assertFormula(solver.mkForall(solver.mkVar(Person, "x"),
    solver.mkTerm(Kind.Implies, Green(solver.mkVar(Person, "x")), Round(solver.mkVar(Person, "x")))))

# Cold and Smart things are Rough
solver.assertFormula(solver.mkForall(solver.mkVar(Person, "x"),
    solver.mkTerm(Kind.And, Cold(solver.mkVar(Person, "x")), Smart(solver.mkVar(Person, "x")),
    Rough(solver.mkVar(Person, "x")))))

# All Round things are Cold
solver.assertFormula(solver.mkForall(solver.mkVar(Person, "x"),
    solver.mkTerm(Kind.Implies, Round(solver.mkVar(Person, "x")), Cold(solver.mkVar(Person, "x")))))

# Bob is Blue
solver.assertFormula(Blue(Bob))

# Charlie is Green
solver.assertFormula(Green(Charlie))

# Charlie is Smart
solver.assertFormula(Smart(Charlie))

# Erin is Rough
solver.assertFormula(Rough(Erin))

# Erin is Smart
solver.assertFormula(Smart(Erin))

# Fiona is Rough
solver.assertFormula(Rough(Fiona))

# Fiona is Smart
solver.assertFormula(Smart(Fiona))

# Test statement: Charlie is not Blue
solver.assertFormula(solver.mkTerm(Kind.Not, Blue(Charlie)))

# Check satisfiability
result = solver.checkSat()

# Print result
print(f"Test Statement Satisfiability: {result}")
```

This code sets up a CVC5 SMT solver instance, declares the necessary sorts, predicates, and individuals, and then asserts each of the given statements as logical formulas in the solver. Finally, it asserts the test statement "Charlie is not blue" as negation of `Blue(Charlie)` and checks its satisfiability. The result will indicate whether the test statement is satisfiable given the provided context.