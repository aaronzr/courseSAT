To generate Python compilable `cvc5` solver formulas based on the constraints from the course requirements document, we'll take the following steps:

1. Define the necessary courses and units.
2. Define the requirements, which include the Technology in Society (TiS) and Writing in the Major (WiM) constraints.
3. Utilize `cvc5` to perform the checks based on provided user input.

Below is the Python code to accomplish this:

```python
from cvc5 import Solver, Kind

# Define the course requirements
course_requirements = [
    "math19",
    "math20",
    "math21",
    "cs103",
    "cs109",
    "phys41",
    "phys43",
    ("math51", "math52", "math53", "math104", "math107", "math108", "math109", "math110", "math113", "cs205l", "cme100", "cme102", "cme104", "engr108"),
    ("cs157", "phil151"),
    "cs106b",
    ("engr40m", "engr76"),
    "cs107",
    "cs111",
    "cs161",
    "cs221",
    ("cs224r", "cs228", "cs229", "cs229m", "cs229t", "cs234", "cs238"),
    ("cs124", "cs224n", "cs224s", "cs224u", "cs224v"),
    ("cs131", "cs231a", "cs231n"),
    ("cs123", "cs223a", "cs237a"),
    ("cs157", "cs205l", "cs230", "cs236", "cs257", "stats315a", "stats315b"),
    ("cs235", "cs279", "cs371"),
    ("cs224w", "cs276"),
    "cs256",
    ("cs151", "cs227b"),
    ("cs225a", "cs327a", "cs329", "engr205", "ms&e251", "ms&e351"),
    ("cs325b", "cs326", "cs329d", "cs330", "cs338", "cs428"),
    ("ee263", "ee278", "ee364a", "ee364b"),
    ("ms&e252", "ms&e352", "ms&e355"),
    ("phil152", "psych204a", "psych204b", "psych209"),
    ("stats200", "stats202", "stats203", "stats205", "stats271"),
    ("cs106b", "cs108", "cs112", "cs123", "cs124", "cs131", "cs140e", "cs142", "cs143", "cs144", "cs145", "cs147", "cs147l", "cs148", "cs149", "cs151", "cs154", "cs155", "cs163", "cs166", "cs168", "cs173a", "cs177", "cs190", "cs195", "cs197", "cs197c", "cs206", "cs210a", "cs212", "cs217", "cs221", "cs223a", "cs224n", "cs224r", "cs224s", "cs224u", "cs224v", "cs224w", "cs225a", "cs227b", "cs228", "cs229", "cs229m", "cs230", "cs231a", "cs231n", "cs232", "cs233", "cs234", "cs235", "cs237a", "cs237b", "cs238", "cs240", "cs240lx", "cs242", "cs243", "cs244", "cs244b", "cs245", "cs246", "cs247", "cs248", "cs249i", "cs250", "cs251", "cs252", "cs253", "cs254", "cs254b", "cs255", "cs256", "cs257", "cs259q", "cs261", "cs263", "cs265", "cs269i", "cs269o", "cs269q", "cs270", "cs271", "cs272", "cs273b", "cs273c", "cs274", "cs275", "cs276", "cs278", "cs279", "cs281", "cs330", "cs333", "cs336", "cs342", "cs348", "cs351", "cs368", "cs398", "cs448b"),
    ("cme108", "ee180", "ee267", "ee282", "ee364a", "ee374", "ms&e234"),
    "cs191",
    ("cs191", "cs191w", "cs194", "cs194h", "cs194w", "cs210b", "cs294"),
    "cs181w",
    "cs182w"
]

# Placeholder for course units for cs181w and cs182w, since units were not provided
cs181w_units = 3  # Assuming 3 units as a placeholder
cs182w_units = 3  # Assuming 3 units as a placeholder

# Example user input of taken courses
course_choices = {
    "cs154": [False, 0],
    "cs140": [True, 3],
    "history244f": [True, 3],
    "cs348a": [True, 3],
    "cs181w": [True, 3],  # Example input for TiS and WiM requirement checking
    "cs182w": [False, 0]  # Not taken
}

# Create a CVC5 solver instance
solver = Solver()
solver.setOption("incremental", "true")

# Assert if the user input satisfies the constraints
for requirement in course_requirements:
    if isinstance(requirement, tuple):
        or_terms = []
        for course in requirement:
            if course in course_choices.keys():
                or_terms.append(solver.mkTerm(Kind.EQUAL, solver.mkBool(course_choices[course][0]), solver.mkTrue()))
        if or_terms:
            solver.assertFormula(solver.mkTerm(Kind.OR, *or_terms))
    else:
        if requirement in course_choices.keys():
            solver.assertFormula(solver.mkTerm(Kind.EQUAL, solver.mkBool(course_choices[requirement][0]), solver.mkTrue()))

# Additional constraints for Technology in Society (TiS) and Writing in the Major (WiM)
tis_wim_courses = ["cs181w", "cs182w"]
tis_wim_taken = [course for course in tis_wim_courses if course_choices.get(course, [False, 0])[0]]
tis_wim_units = sum(course_choices[course][1] for course in tis_wim_courses if course_choices.get(course, [False, 0])[0])

# Assert the constraints
if tis_wim_units >= 3:
    solver.assertFormula(solver.mkBool(True))  # Assert that at least 3 units are taken from TiS/WiM courses
else:
    solver.assertFormula(solver.mkBool(False))

# Check satisfiability
if solver.checkSat().isSat():
    print("The course choices satisfy all the constraints.")
else:
    print("The course choices do not satisfy all the constraints.")
```

This code dynamically constructs the constraint formulas based on the provided document structure. It uses `cvc5` to check if the courses taken by the user satisfy the program requirements, including the Technology in Society (TiS) and Writing in the Major (WiM) constraints. Note that placeholders for course unit values are assumed for "cs181w" and "cs182w" due to lack of specific unit information. Adjust these as per actual data.