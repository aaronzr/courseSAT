
import cvc5
from cvc5 import Kind

# Create a solver instance
solver = cvc5.Solver()
solver.setOption("produce-models", "true")  # Ensure models are produced
