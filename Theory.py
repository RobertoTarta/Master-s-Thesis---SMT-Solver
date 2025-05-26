

from z3 import *

class TheorySolver:
    def __init__(self):
        self.constraints = []
        self.solver = Solver()
        self.variables = {}

    def add_variable(self, name, sort):
        #add variable with given name and sort ( Int, Bool, Real)
        if sort == "Int":
            var = Int(name)
        elif sort == "Real":
            var = Real(name)
        elif sort == "Bool":
            var = Bool(name)
        else:
            raise ValueError(f"Unsupported sort: {sort}")
        self.variables[name] = var
        return var

    def add_constraint(self, constraint):
        #add theory constraint
        self.constraints.append(constraint)
        self.solver.add(constraint)

    def check(self):
        #check satisfiability of constraints
        result = self.solver.check()
        if result == sat:
            return "SAT", self.solver.model()
        elif result == unsat:
            return "UNSAT", None
        else:
            return "UNKNOWN", None

    def get_model(self):
        #return model if constraints are sat
        if self.solver.check() == sat:
            return self.solver.model()
        return None

    def get_variables(self):
        #return dictionary of variables
        return self.variables


if __name__ == "__main__":
    ts = TheorySolver()

    # variables
    x = ts.add_variable("x", "Int")
    y = ts.add_variable("y", "Int")

    # constraints
    ts.add_constraint(x + y > 0)
    ts.add_constraint(x - y < 5)
    ts.add_constraint(x >= 0)

    # Check satisfiability
    result, model = ts.check()
    print(f"Result: {result}")
    if model:
        print("Model:")
        for var in model:
            print(f"  {var} = {model[var]}")