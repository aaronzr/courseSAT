Sure, let's go through each statement and translate them into CVC5 Python formulas step by step. I will also provide the final test script to evaluate the test statement "Dave is green."

First, let's import cvc5 and create the necessary solver and boolean variables:

```python
from cvc5 import Solver, Kind

solver = Solver()
solver.setOption("produce-models", "true")

# Define sorts
Bool = solver.getBooleanSort()

# Define parameters
is_white = solver.mkConst(Bool, "is_white")
is_quiet = solver.mkConst(Bool, "is_quiet")
is_young = solver.mkConst(Bool, "is_young")
is_green = solver.mkConst(Bool, "is_green")
is_round = solver.mkConst(Bool, "is_round")
is_kind = solver.mkConst(Bool, "is_kind")
is_furry = solver.mkConst(Bool, "is_furry")
is_dave_quiet = solver.mkConst(Bool, "is_dave_quiet")
is_dave_furry = solver.mkConst(Bool, "is_dave_furry")
is_bob_furry = solver.mkConst(Bool, "is_bob_furry")
is_bob_quiet = solver.mkConst(Bool, "is_bob_quiet")
is_charlie_furry = solver.mkConst(Bool, "is_charlie_furry")
is_charlie_kind = solver.mkConst(Bool, "is_charlie_kind")
is_dave_green = solver.mkConst(Bool, "is_dave_green")
is_dave_kind = solver.mkConst(Bool, "is_dave_kind")
is_dave_round = solver.mkConst(Bool, "is_dave_round")
is_dave_white = solver.mkConst(Bool, "is_dave_white")
is_dave_young = solver.mkConst(Bool, "is_dave_young")
is_gary_furry = solver.mkConst(Bool, "is_gary_furry")
is_gary_green = solver.mkConst(Bool, "is_gary_green")
```

Now, let's define each statement:

1. 'If something is white then it is not quiet.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_white, solver.mkTerm(Kind.NOT, is_quiet)))
```

2. 'All young, green things are round.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_young, is_green), is_round))
```

3. 'All green, white things are kind.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_green, is_white), is_kind))
```

4. 'If something is young and not furry then it is kind.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_young, solver.mkTerm(Kind.NOT, is_furry)), is_kind))
```

5. 'All round, green things are kind.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_round, is_green), is_kind))
```

6. 'If Charlie is white then Charlie is green.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_white, is_green))
```

7. 'Kind, green things are white.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_kind, is_green), is_white))
```

8. 'All furry things are young.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_furry, is_young))
```

9. 'If Dave is quiet and Dave is furry then Dave is not kind.'
```python
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_dave_quiet, is_dave_furry), solver.mkTerm(Kind.NOT, is_dave_kind))
```

10. 'Bob is not furry.'
```python
solver.assertFormula(solver.mkTerm(Kind.NOT, is_bob_furry))
```

11. 'Bob is quiet.'
```python
solver.assertFormula(is_bob_quiet)
```

12. 'Charlie is furry.'
```python
solver.assertFormula(is_charlie_furry)
```

13. 'Charlie is kind.'
```python
solver.assertFormula(is_charlie_kind)
```

14. 'Dave is green.'
```python
solver.assertFormula(is_dave_green)
```

15. 'Dave is kind.'
```python
solver.assertFormula(is_dave_kind)
```

16. 'Dave is round.'
```python
solver.assertFormula(is_dave_round)
```

17. 'Dave is white.'
```python
solver.assertFormula(is_dave_white)
```

18. 'Dave is young.'
```python
solver.assertFormula(is_dave_young)
```

19. 'Gary is furry.'
```python
solver.assertFormula(is_gary_furry)
```

20. 'Gary is green.'
```python
solver.assertFormula(is_gary_green)
```

Finally, let's evaluate the test statement "Dave is green."

```python
# We'll check if the solver can assert the value of Dave being green
solver.checkSatAssuming(is_dave_green) == solver.checkSat(True)
```

Putting it all together:

```python
from cvc5 import Solver, Kind

solver = Solver()
solver.setOption("produce-models", "true")

Bool = solver.getBooleanSort()

is_white = solver.mkConst(Bool, "is_white")
is_quiet = solver.mkConst(Bool, "is_quiet")
is_young = solver.mkConst(Bool, "is_young")
is_green = solver.mkConst(Bool, "is_green")
is_round = solver.mkConst(Bool, "is_round")
is_kind = solver.mkConst(Bool, "is_kind")
is_furry = solver.mkConst(Bool, "is_furry")
is_dave_quiet = solver.mkConst(Bool, "is_dave_quiet")
is_dave_furry = solver.mkConst(Bool, "is_dave_furry")
is_bob_furry = solver.mkConst(Bool, "is_bob_furry")
is_bob_quiet = solver.mkConst(Bool, "is_bob_quiet")
is_charlie_furry = solver.mkConst(Bool, "is_charlie_furry")
is_charlie_kind = solver.mkConst(Bool, "is_charlie_kind")
is_dave_green = solver.mkConst(Bool, "is_dave_green")
is_dave_kind = solver.mkConst(Bool, "is_dave_kind")
is_dave_round = solver.mkConst(Bool, "is_dave_round")
is_dave_white = solver.mkConst(Bool, "is_dave_white")
is_dave_young = solver.mkConst(Bool, "is_dave_young")
is_gary_furry = solver.mkConst(Bool, "is_gary_furry")
is_gary_green = solver.mkConst(Bool, "is_gary_green")

solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_white, solver.mkTerm(Kind.NOT, is_quiet)))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_young, is_green), is_round))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_green, is_white), is_kind))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_young, solver.mkTerm(Kind.NOT, is_furry)), is_kind))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_round, is_green), is_kind))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_white, is_green))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_kind, is_green), is_white))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, is_furry, is_young))
solver.assertFormula(solver.mkTerm(Kind.IMPLIES, solver.mkTerm(Kind.AND, is_dave_quiet, is_dave_furry), solver.mkTerm(Kind.NOT, is_dave_kind)))
solver.assertFormula(solver.mkTerm(Kind.NOT, is_bob_furry))
solver.assertFormula(is_bob_quiet)
solver.assertFormula(is_charlie_furry)
solver.assertFormula(is_charlie_kind)
solver.assertFormula(is_dave_green)
solver.assertFormula(is_dave_kind)
solver.assertFormula(is_dave_round)
solver.assertFormula(is_dave_white)
solver.assertFormula(is_dave_young)
solver.assertFormula(is_gary_furry)
solver.assertFormula(is_gary_green)

result = solver.checkSatAssuming(is_dave_green)
print(f"The statement 'Dave is green.' is {result}")
```

With this Python script, you should be able to use the CVC5 SMT solver to evaluate the given statements and the test statement "Dave is green."