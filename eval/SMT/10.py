
import cvc5
from cvc5 import Term

# Initialize the solver
slv = cvc5.Solver()

# Set the logic
slv.setLogic("QF_LIA")

# Define the variable slots
slots = {}
for c in ['Q', 'R', 'S', 'T', 'U']:
    for m in range(1, 4):
        slots[(c, m)] = slv.mkConst(slv.getIntegerSort(), f'slot_{c}_{m}')

# Declare some useful constants
zero = slv.mkInteger(0)
one = slv.mkInteger(1)
two = slv.mkInteger(2)
three = slv.mkInteger(3)
four = slv.mkInteger(4)
five = slv.mkInteger(5)

# Constraint: No two candidates will speak in the same time slot at any meeting
for m in range(1, 4):
    for c1 in ['Q', 'R', 'S', 'T', 'U']:
        for c2 in ['Q', 'R', 'S', 'T', 'U']:
            if c1 != c2:
                slv.assertFormula(slv.mkTerm(cvc5.Kind.DISTINCT, slots[(c1, m)], slots[(c2, m)]))

# Constraint: Each candidate must speak either first or second at at least one of the meetings
for c in ['Q', 'R', 'S', 'T', 'U']:
    slv.assertFormula(
        slv.mkTerm(
            cvc5.Kind.OR,
            slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, 1)], one),
            slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, 1)], two),
            slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, 2)], one),
            slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, 2)], two),
            slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, 3)], one),
            slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, 3)], two)
        )
    )

# Constraint: Any candidate who speaks fifth at any of the meetings must speak first at at least one of the other meetings
for c in ['Q', 'R', 'S', 'T', 'U']:
    for m in range(1, 4):
        slv.assertFormula(
            slv.mkTerm(
                cvc5.Kind.IMPLIES,
                slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, m)], five),
                slv.mkTerm(
                    cvc5.Kind.OR,
                    *[slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, m_prime)], one) for m_prime in range(1, 4) if m_prime != m]
                )
            )
        )

# Constraint: No candidate can speak fourth at more than one of the meetings
for c in ['Q', 'R', 'S', 'T', 'U']:
    slv.assertFormula(
        slv.mkTerm(
            cvc5.Kind.LEQ,
            slv.mkTerm(
                cvc5.Kind.ADD,
                *[slv.mkTerm(
                    cvc5.Kind.ITE,
                    slv.mkTerm(cvc5.Kind.EQUAL, slots[(c, m)], four),
                    one,
                    zero
                ) for m in range(1, 4)]
            ),
            one
        )
    )

# Given condition: R speaks second at meeting 2 and first at meeting 3
slv.assertFormula(slv.mkTerm(cvc5.Kind.EQUAL, slots[('R', 2)], two))
slv.assertFormula(slv.mkTerm(cvc5.Kind.EQUAL, slots[('R', 3)], one))

# Determine the slots for R at meeting 1
def check_slot(slot_value):
    assumption = slv.mkTerm(cvc5.Kind.EQUAL, slots[('R', 1)], slot_value)
    result = slv.checkSatAssuming(assumption)
    return result.isSat()

possible_slots = []
for slot in [one, two, three, four, five]:
    if check_slot(slot):
        possible_slots.append(slot)

# Extract integer values directly from the terms
possible_slots_values = [slot.getIntegerValue() for slot in possible_slots]

# Convert to integers
possible_slots_values = [int(value) for value in possible_slots_values]

# Print the possible slots
print(possible_slots_values)
