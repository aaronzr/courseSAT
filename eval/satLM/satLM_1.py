To encode the given problem statement in Z3Py (a Python API for the Z3 theorem prover), you can follow these steps:

1. Declare the enum sets for experts and languages.
2. Define the positions for the presentations.
3. Set up the constraints as specified in the problem statement.
4. Define the solution choices and check which one satisfies all the constraints.

Here is the complete Z3Py code for the given file:

```python
from z3 import *

# Declare the experts
experts = ["lawyer", "naturalist", "oceanographer", "physicist", "statistician"]

# Declare the languages
languages = ["French", "Hindi", "Japanese", "Mandarin"]

# Define positions
positions = [Int(f"pos_{exp}") for exp in experts]

# Define the language spoken at each position
spoken_languages = [Int(f"lang_{i}") for i in range(5)]

# Create a solver instance
solver = Solver()

# Adding constraints for positions and languages
for pos in positions:
    solver.add(And(pos >= 1, pos <= 5)) # Each position is between 1 and 5

solver.add(Distinct(positions)) # All positions are distinct
for lang in spoken_languages:
    solver.add(And(lang >= 0, lang <= 3)) # Each language index is between 0 and 3

# Mapping to use languages by indices to ease constraints application
lang_index = {lang: i for i, lang in enumerate(languages)}

# Constraint: Exactly two of the presentations are in the same language
language_counts = [Sum([If(spoken_languages[i] == j, 1, 0) for i in range(5)]) for j in range(4)]
solver.add(Sum([If(count == 2, 1, 0) for count in language_counts]) == 1)

# Constraint: The statistician gives the second presentation in Hindi
statistician_pos = positions[experts.index("statistician")]
solver.add(statistician_pos == 2)
solver.add(spoken_languages[1] == lang_index["Hindi"])

# Constraint: The lawyer gives the fourth presentation in either Mandarin or French
lawyer_pos = positions[experts.index("lawyer")]
solver.add(lawyer_pos == 4)
solver.add(Or(spoken_languages[3] == lang_index["Mandarin"], spoken_languages[3] == lang_index["French"]))

# Constraint: The oceanographer presents in either French or Japanese; the same is true of the physicist
oceanographer_pos = positions[experts.index("oceanographer")]
physicist_pos = positions[experts.index("physicist")]
solver.add(Or(spoken_languages[oceanographer_pos - 1] == lang_index["French"], spoken_languages[oceanographer_pos - 1] == lang_index["Japanese"]))
solver.add(Or(spoken_languages[physicist_pos - 1] == lang_index["French"], spoken_languages[physicist_pos - 1] == lang_index["Japanese"]))

# Constraint: The first presentation and the last presentation are in Japanese
solver.add(spoken_languages[0] == lang_index["Japanese"])
solver.add(spoken_languages[4] == lang_index["Japanese"])

# Define the solution choices
choices = [
    ("A", ["physicist", "statistician", "lawyer", "naturalist", "oceanographer"]),
    ("B", ["physicist", "naturalist", "oceanographer", "lawyer", "statistician"]),
    ("C", ["oceanographer", "statistician", "naturalist", "lawyer", "physicist"]),
    ("D", ["oceanographer", "statistician", "lawyer", "naturalist", "physicist"]),
]

# Check each choice to find the valid one
for choice_label, choice in choices:
    choice_pos = [positions[experts.index(exp)] for exp in choice]
    solver.push()
    solver.add([position == index + 1 for index, position in enumerate(choice_pos)])

    if solver.check() == sat:
        print(f"Choice {choice_label} is valid")
    else:
        print(f"Choice {choice_label} is not valid")

    solver.pop()
```

In this code:

- We declare the experts and languages.
- We define the positions of the presentations and the languages spoken at each position.
- We add constraints based on the given conditions.
- We then check which of the given choices satisfy all the constraints and print the valid one(s).

Note that this solution assumes that the language indices start from 0 to 3 for "French", "Hindi", "Japanese", and "Mandarin" respectively.