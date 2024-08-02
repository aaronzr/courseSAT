Below is a Python script that uses Z3 to encode the constraints and solve the problem provided:

```python
from z3 import *

# Declare experts
experts = ["lawyer", "naturalist", "oceanographer", "physicist", "statistician"]
positions = [1, 2, 3, 4, 5]

# Declare languages
languages = ["French", "Hindi", "Japanese", "Mandarin"]

# Map experts to their positions
expert_pos = {expert: Int(expert) for expert in experts}

# Presentation language at each position
lang_at_pos = {pos: Int(f"lang_{pos}") for pos in positions}

# Create the solver
s = Solver()

# Each expert must be in a different position
s.add(Distinct([expert_pos[expert] for expert in experts]))

# Positions are between 1 and 5
for pos in expert_pos.values():
    s.add(And(pos >= 1, pos <= 5))

# Each position must have exactly one language
for pos in positions:
    s.add(Or([lang_at_pos[pos] == languages.index(lang) for lang in languages]))

# Exactly two of the presentations are in the same language
s.add(Sum([If(lang_at_pos[i] == lang_at_pos[j], 1, 0) for i in positions for j in positions if i < j]) == 1)

# The statistician gives the second presentation in Hindi
s.add(expert_pos["statistician"] == 2)
s.add(lang_at_pos[2] == languages.index("Hindi"))

# The lawyer gives the fourth presentation in either Mandarin or French
s.add(expert_pos["lawyer"] == 4)
s.add(Or(lang_at_pos[4] == languages.index("Mandarin"), lang_at_pos[4] == languages.index("French")))

# The oceanographer presents in either French or Japanese; the same is true of the physicist
s.add(Or(lang_at_pos[expert_pos["oceanographer"]] == languages.index("French"), lang_at_pos[expert_pos["oceanographer"]] == languages.index("Japanese")))
s.add(Or(lang_at_pos[expert_pos["physicist"]] == languages.index("French"), lang_at_pos[expert_pos["physicist"]] == languages.index("Japanese")))

# The first presentation and the last presentation are in Japanese
s.add(lang_at_pos[1] == languages.index("Japanese"))
s.add(lang_at_pos[5] == languages.index("Japanese"))

# Possible orders to check
orders = [
    ("physicist", "statistician", "lawyer", "naturalist", "oceanographer"),
    ("physicist", "naturalist", "oceanographer", "lawyer", "statistician"),
    ("oceanographer", "statistician", "naturalist", "lawyer", "physicist"),
    ("oceanographer", "statistician", "lawyer", "naturalist", "physicist")
]

# Check each possible order
for order in orders:
    s.push()
    for i, expert in enumerate(order):
        s.add(expert_pos[expert] == i + 1)
    if s.check() == sat:
        m = s.model()
        print(f"Order {order} could be valid with languages:")
        for pos in positions:
            lang = m[lang_at_pos[pos]]
            print(f" Position {pos}: {languages[lang.as_long()]}")
        break
    s.pop()
else:
    print("No valid order found")
```

This script sets up the problem constraints using Z3, tests each possible order for the experts, and checks whether it satisfies all given constraints. If a valid order is found, it prints the order and the languages used in each position. If no valid order is found, it prints that no valid order was found.