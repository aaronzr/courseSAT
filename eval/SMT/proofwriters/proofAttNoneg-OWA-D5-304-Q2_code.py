Sure, I will translate each of the given statements into CVC5 SMT Python formulas. Let's initialize the CVC5 environment first:

```python
import cvc5
from cvc5 import Kind

# Initialize the solver
solver = cvc5.Solver()

# Define Boolean sorts
boolean = solver.getBooleanSort()

# Define the variables
dave_green = solver.mkConst(boolean, 'DaveGreen')
dave_white = solver.mkConst(boolean, 'DaveWhite')
dave_blue = solver.mkConst(boolean, 'DaveBlue')

something_green = solver.mkVar(boolean, 'somethingGreen')
something_nice = solver.mkVar(boolean, 'somethingNice')

something_blue = solver.mkVar(boolean, 'somethingBlue')
something_cold = solver.mkVar(boolean, 'somethingCold')

something_white = solver.mkVar(boolean, 'somethingWhite')
something_young = solver.mkVar(boolean, 'somethingYoung')

something_kind = solver.mkVar(boolean, 'somethingKind')

anne_cold = solver.mkConst(boolean, 'AnneCold')
anne_kind = solver.mkConst(boolean, 'AnneKind')

charlie_nice = solver.mkConst(boolean, 'CharlieNice')

fiona_blue = solver.mkConst(boolean, 'FionaBlue')
fiona_white = solver.mkConst(boolean, 'FionaWhite')
```

1. **If Dave is green and Dave is white then Dave is blue.**
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, dave_green, dave_white), dave_blue))
```

2. **If something is green then it is nice.**
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, something_green, something_nice))
```

3. **If something is blue and cold then it is green.**
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, something_blue, something_cold), something_green))
```

4. **If something is white and young then it is kind.**
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, something_white, something_young), something_kind))
```

5. **If something is cold then it is blue.**
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, something_cold, something_blue))
```

6. **All nice, kind things are green.**
```python
nice_and_kind = solver.mkTerm(Kind.AND, something_nice, something_kind)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, nice_and_kind, something_green))
```

7. **All kind, cold things are white.**
```python
kind_and_cold = solver.mkTerm(Kind.AND, something_kind, something_cold)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, kind_and_cold, something_white))
```

8. **If something is kind and young then it is cold.**
```python
kind_and_young = solver.mkTerm(Kind.AND, something_kind, something_young)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, kind_and_young, something_cold))
```

9. **Anne is cold.**
```python
solver.assertFormula(anne_cold)
```

10. **Anne is kind.**
```python
solver.assertFormula(anne_kind)
```

11. **Charlie is nice.**
```python
solver.assertFormula(charlie_nice)
```

12. **Dave is white.**
```python
solver.assertFormula(dave_white)
```

13. **Dave is young.**
```python
dave_young = solver.mkConst(boolean, 'DaveYoung')
solver.assertFormula(dave_young)
```

14. **Fiona is blue.**
```python
solver.assertFormula(fiona_blue)
```

15. **Fiona is white.**
```python
solver.assertFormula(fiona_white)
```

**Test Statement: Charlie is not nice.**
```python
charlie_not_nice = solver.mkTerm(Kind.NOT, charlie_nice)
```

Let's check the satisfiability of the test statement:

```python
solver.push()  # Save the current state
solver.assertFormula(charlie_not_nice)
result = solver.checkSat()

if result.isSat():
    print("Charlie is not nice is satisfiable.")
else:
    print("Charlie is not nice is not satisfiable.")
solver.pop()  # Restore the state
```

Let's run this code in totality to ensure the logic and syntax are correct:

```python
import cvc5
from cvc5 import Kind

# Initialize the solver
solver = cvc5.Solver()

# Define Boolean sorts
boolean = solver.getBooleanSort()

# Define the variables
dave_green = solver.mkConst(boolean, 'DaveGreen')
dave_white = solver.mkConst(boolean, 'DaveWhite')
dave_blue = solver.mkConst(boolean, 'DaveBlue')

something_green = solver.mkVar(boolean, 'somethingGreen')
something_nice = solver.mkVar(boolean, 'somethingNice')

something_blue = solver.mkVar(boolean, 'somethingBlue')
something_cold = solver.mkVar(boolean, 'somethingCold')

something_white = solver.mkVar(boolean, 'somethingWhite')
something_young = solver.mkVar(boolean, 'somethingYoung')

something_kind = solver.mkVar(boolean, 'somethingKind')

anne_cold = solver.mkConst(boolean, 'AnneCold')
anne_kind = solver.mkConst(boolean, 'AnneKind')

charlie_nice = solver.mkConst(boolean, 'CharlieNice')

dave_young = solver.mkConst(boolean, 'DaveYoung')

fiona_blue = solver.mkConst(boolean, 'FionaBlue')
fiona_white = solver.mkConst(boolean, 'FionaWhite')

# Define and assert the formulas
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, dave_green, dave_white), dave_blue))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, something_green, something_nice))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, something_blue, something_cold), something_green))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, something_white, something_young), something_kind))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, something_cold, something_blue))
nice_and_kind = solver.mkTerm(Kind.AND, something_nice, something_kind)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, nice_and_kind, something_green))
kind_and_cold = solver.mkTerm(Kind.AND, something_kind, something_cold)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, kind_and_cold, something_white))
kind_and_young = solver.mkTerm(Kind.AND, something_kind, something_young)
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, kind_and_young, something_cold))
solver.assertFormula(anne_cold)
solver.assertFormula(anne_kind)
solver.assertFormula(charlie_nice)
solver.assertFormula(dave_white)
solver.assertFormula(dave_young)
solver.assertFormula(fiona_blue)
solver.assertFormula(fiona_white)

# Test statement: Charlie is not nice
charlie_not_nice = solver.mkTerm(Kind.NOT, charlie_nice)

solver.push()  # Save the current state
solver.assertFormula(charlie_not_nice)
result = solver.checkSat()

if result.isSat():
    print("Charlie is not nice is satisfiable.")
else:
    print("Charlie is not nice is not satisfiable.")
solver.pop()  # Restore the state
```