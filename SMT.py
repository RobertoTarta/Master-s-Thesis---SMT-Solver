import os
import re
from collections import defaultdict
import random
from z3 import *

# CDCL Solver
def pigeonhole_principle(n):
    def var(i, j):
        return i * n + j + 1
    for i in range(1, n + 2):
        yield [var(i, j) for j in range(1, n + 1)]
    for j in range(1, n + 1):
        for i1 in range(1, n + 2):
            for i2 in range(i1 + 1, n + 2):
                yield [-var(i1, j), -var(i2, j)]

def unit_propagation(clauses, learned_clauses, assignments, decision_stack, level):
    while True:
        unit_found = False
        for clause in clauses + learned_clauses:
            unassigned = [lit for lit in clause if lit not in assignments and -lit not in assignments]
            assigned_true = any(assignments.get(lit, False) for lit in clause)
            if assigned_true:
                continue
            if not unassigned and not assigned_true:
                return clause
            if len(unassigned) == 1:
                lit = unassigned[0]
                assignments[lit] = True
                decision_stack.append((lit, level, "implied"))
                unit_found = True
                break
        if not unit_found:
            return None

def analyze_conflict(conflict_clause, assignments, decision_stack, level, vsids_scores=None):
    if level == 0:
        return None, -1
    conflict_vars = set(abs(lit) for lit in conflict_clause)
    relevant_decisions = set()
    for lit, lvl, reason in reversed(decision_stack):
        if lvl > level:
            continue
        if reason == "decision":
            if abs(lit) in conflict_vars or any(abs(l) in conflict_vars for l, l_lvl, r in decision_stack if l_lvl == lvl and r == "implied"):
                relevant_decisions.add(lit)
    learned_clause = []
    for lit in relevant_decisions:
        negated_lit = -lit if assignments.get(lit, False) else lit
        learned_clause.append(negated_lit)
        if vsids_scores is not None:
            vsids_scores[abs(lit)] += 1
    if not learned_clause:
        if not decision_stack:
            return None, -1
        last_decision = next((lit for lit, lvl, r in reversed(decision_stack) if r == "decision" and lvl == level), None)
        if last_decision:
            learned_clause = [-last_decision if assignments.get(last_decision, False) else last_decision]
    levels = sorted([lvl for lit, lvl, r in decision_stack if r == "decision" and (lit in relevant_decisions or lit in [abs(l) if l > 0 else -l for l in learned_clause])], reverse=True)
    backtrack_level = levels[1] if len(levels) > 1 else 0
    return learned_clause, backtrack_level

def backtrack(decision_stack, assignments, level):
    decision_stack[:] = [(lit, lvl, reason) for lit, lvl, reason in decision_stack if lvl <= level]
    assignments.clear()
    for lit, _, _ in decision_stack:
        assignments[lit] = True

def decide(clauses, assignments, decision_stack, level, strategy="first", vsids_scores=None):
    unassigned_vars = set()
    var_count = defaultdict(int)
    for clause in clauses:
        for lit in clause:
            if lit not in assignments and -lit not in assignments:
                unassigned_vars.add(lit)
                var_count[lit] += 1
    if not unassigned_vars:
        return False, level
    level += 1
    if strategy == "first":
        lit = min(unassigned_vars)
    elif strategy == "random":
        lit = random.choice(list(unassigned_vars))
    elif strategy == "frequent":
        lit = max(var_count.items(), key=lambda x: x[1])[0]
    elif strategy == "vsids" and vsids_scores:
        lit = max(unassigned_vars, key=lambda l: vsids_scores.get(abs(l), 0))
    else:
        lit = min(unassigned_vars)
    assignments[lit] = True
    decision_stack.append((lit, level, "decision"))
    return True, level

def solve_cdcl(clauses, branching_strategy="first", max_conflicts=10000):
    assignments = {}
    decision_stack = []
    learned_clauses = []
    level = 0
    vsids_scores = defaultdict(float) if branching_strategy == "vsids" else None
    conflict_count = 0
    decay_factor = 0.95
    decay_interval = 10
    if vsids_scores:
        for clause in clauses:
            for lit in clause:
                vsids_scores[abs(lit)] += 0.1
    while conflict_count < max_conflicts:
        conflict = unit_propagation(clauses, learned_clauses, assignments, decision_stack, level)
        if conflict is not None:
            conflict_count += 1
            learned_clause, backtrack_level = analyze_conflict(conflict, assignments, decision_stack, level, vsids_scores)
            if backtrack_level < 0:
                return "UNSAT", None
            learned_clauses.append(learned_clause)
            backtrack(decision_stack, assignments, backtrack_level)
            level = backtrack_level
            if vsids_scores and conflict_count % decay_interval == 0:
                for var in vsids_scores:
                    vsids_scores[var] *= decay_factor
        else:
            decided, new_level = decide(clauses, assignments, decision_stack, level, branching_strategy, vsids_scores)
            if not decided:
                if not clauses:
                    return "SAT", {}
                max_var = max(abs(lit) for clause in clauses for lit in clause)
                solution = {i: assignments.get(i, False) or not assignments.get(-i, False) for i in range(1, max_var + 1)}
                return "SAT", solution
            level = new_level
    return "TIMEOUT", None

# Theory Solver
class TheorySolver:
    def __init__(self):
        self.constraints = []
        self.solver = Solver()
        self.variables = {}

    def add_variable(self, name, sort):
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
        self.constraints.append(constraint)
        self.solver.add(constraint)

    def check(self):
        result = self.solver.check()
        if result == sat:
            return "SAT", self.solver.model()
        elif result == unsat:
            return "UNSAT", None
        else:
            return "UNKNOWN", None

    def get_model(self):
        if self.solver.check() == sat:
            return self.solver.model()
        return None

    def get_variables(self):
        return self.variables

# SMT-LIB Parser
class SMTLIBParser:
    def __init__(self):
        self.variables = {}  # store variable info -> (sort, propositional_var_id)
        self.clauses = []    # propositional clauses for CDCL
        self.theory_constraints = []  # theory constraints for theory solver
        self.var_counter = 1  # for assigning unique propositional variable IDs
        self.var_map = {}     # maps variables to unique propositional variable IDs
        self.expected_status = None # expected results read from files

    def parse(self, smt_file_content):
        lines = smt_file_content.splitlines() #split content into lines
        for line in lines:
            line = line.strip() #delete empty spaces
            if not line or line.startswith(';'):
                continue
            if line.startswith('(set-info :status'):
                self.parse_set_info_status(line)
                continue
            if line.startswith('(set-logic QF_LIA'):
                continue
            if line.startswith('(exit'): #if starts with any of these texts, skip
                continue
            if line.startswith('(declare-fun'):
                self.parse_declare_fun(line) #if declare fun command is read
            elif line.startswith('(declare-const'):
                self.parse_declare_const(line) #if declare const command is read
            elif line.startswith('(assert'):
                self.parse_assert(line) #if assert command is read
            elif line.startswith('(check-sat)') or line.startswith('(get-model)'):
                continue #skips these lines
            else:
                pass

    def parse_set_info_status(self, line):
        match = re.search(r'\(set-info\s+:status\s+([^\s\)]+)\)', line) #extract expected result
        if match:
            self.expected_status = match.group(1).strip()

    def parse_declare_const(self, line):
        match = re.match(r'\(declare-const\s+([^\s]+)\s+([^\s]+)\)', line) #extract const info
        if not match:
            raise ValueError(f"Invalid declare-const: {line}")
        var_name, sort = match.groups()
        self.variables[var_name] = (sort, self.var_counter)
        self.var_map[var_name] = self.var_counter
        self.var_counter += 1

    def parse_declare_fun(self, line):
        match = re.match(r'\(declare-fun\s+([^\s]+)\s+\(\)\s+([^\s]+)\)', line) #extract variable ifo
        if not match:
            raise ValueError(f"Invalid declare-fun: {line}")
        var_name, sort = match.groups()
        self.variables[var_name] = (sort, self.var_counter)
        self.var_map[var_name] = self.var_counter
        self.var_counter += 1

    def tokenize(self, expr):
        #tokenize an SMT-LIB expression, preserving parentheses, ex: "< 5 x" -> ["<","5","x"]
        tokens = []
        i = 0
        while i < len(expr):
            if expr[i].isspace():
                i += 1
                continue
            if expr[i] in '()':
                tokens.append(expr[i])
                i += 1
                continue
            if expr[i] == ';':
                break  # skip comments
            start = i
            while i < len(expr) and not expr[i].isspace() and expr[i] not in '()':
                i += 1
            tokens.append(expr[start:i])
        return tokens

    def parse_sexpr(self, tokens, start):
        #parse an S-expression into a nested list structure ex: ['(', 'and', '(', '<', 'x', '5', ')', '(', '>', 'y', '2', ')', ')'] -> ['and', ['<', 'x', '5'], ['>', 'y', '2']]
        if start >= len(tokens):
            raise ValueError("Unexpected end of tokens")
        if tokens[start] != '(':
            return tokens[start], start + 1
        start += 1
        result = []
        while start < len(tokens) and tokens[start] != ')':
            subexpr, next_start = self.parse_sexpr(tokens, start)
            result.append(subexpr)
            start = next_start
        if start >= len(tokens) or tokens[start] != ')':
            raise ValueError("Mismatched parentheses")
        return result, start + 1

    def parse_assert(self, line):
       #parse asserts, calls tokenize and parse_sexpr then sends the expression as input to handle_assertion_expr
        match = re.match(r'\(assert\s+(.+)\)', line)
        if not match:
            raise ValueError(f"Invalid assert: {line}")
        constraint = match.group(1).strip()
        tokens = self.tokenize(constraint)
        expr, _ = self.parse_sexpr(tokens, 0)

        self._handle_assertion_expr(expr)


    def _handle_assertion_expr(self, expr):
        if isinstance(expr, str): #if expression is a string
            if expr in ['true', 'false']:  #if assert is "true" or "false" -> "(assert true)"
                var_id = self.var_map.get(expr, self.var_counter) #looks up its ID
                if expr == 'true':
                    self.clauses.append([var_id]) #assigns id as true
                else:
                    self.clauses.append([-var_id]) #assigns id as false
                if expr not in self.variables: #if it wasnt assigned before
                    self.variables[expr] = ('Bool', var_id)
                    self.var_map[expr] = var_id #maps new id
                    self.var_counter += 1
            elif expr in self.var_map: #if its a mapped variable ex: (assert x) -> means x is true
                var_id = self.var_map[expr]
                self.clauses.append([var_id]) #assign id as true
            else:
                pass
        elif isinstance(expr, list): #if its a list
            op = expr[0]
            if op == 'not': #if its an not assert ex: (assert (not x))
                if len(expr) != 2 or expr[1] not in self.var_map:
                    raise ValueError(f"Invalid not constraint: {expr}")
                var_id = self.var_map[expr[1]]
                self.clauses.append([-var_id]) #assert variable as false
            elif op == 'and': #handles "and" in asserts
                if len(expr) < 2:
                    raise ValueError(f"Invalid and constraint: {expr}")
                for sub_expr in expr[1:]:
                    self._handle_assertion_expr(sub_expr) #calls handle assertion for each var ex: (assert (and x y z)) -> calls
                                                          #_handle_assertion_expr(x), _handle_assertion_expr(y), _handle_assertion_expr(z)
                                                          #assigning them as true
            elif op == 'or': #handles "or" in asserts
                if len(expr) < 2:
                    raise ValueError(f"Invalid or constraint: {expr}")
                or_clause = []
                for sub_expr in expr[1:]: #at least one of the vars must be true
                    if isinstance(sub_expr, str) and sub_expr in self.var_map:
                        or_clause.append(self.var_map[sub_expr])
                    elif isinstance(sub_expr, list) and sub_expr[0] == 'not' and len(sub_expr) == 2 and sub_expr[1] in self.var_map:
                        or_clause.append(-self.var_map[sub_expr[1]])
                    else:
                        self.theory_constraints.append(sub_expr) #if containts arithmetic terms, add to contraints ex: x < 5 can't be assigned as true or false

                if or_clause:
                    self.clauses.append(or_clause)
            elif op in ['=', '>', '<', '>=', '<=', '+', '*', '-']: #handles arithmetic asserts
                 self.theory_constraints.append(expr)
            else:
                # recursively parse other nested S-expressions if needed
                for sub_expr in expr:
                    if isinstance(sub_expr, (str, list)):
                         self._handle_assertion_expr(sub_expr)
        else:
             raise ValueError(f"Unsupported assertion type: {expr}")

#OUTPUT HELPERS

    def get_clauses(self):
        return self.clauses

    def get_theory_constraints(self):
        return self.theory_constraints

    def get_variables(self):
        return self.variables

    def get_expected_status(self):
        return self.expected_status


class SMTSolver:
    def __init__(self):
        self.parser = SMTLIBParser()
        self.theory_solver = TheorySolver()
        self.clauses = [] #stores sat clauses
        self.variables = {} #maps variables
        self.theory_constraints = [] #stores arithmetic constraints
        self.expected_status = None # stores expected result

    def load_smt_file(self, smt_file_content): #extract data from files and save in solver
        self.parser.parse(smt_file_content)
        self.clauses = self.parser.get_clauses()
        self.theory_constraints = self.parser.get_theory_constraints()
        self.variables = self.parser.get_variables()
        self.expected_status = self.parser.get_expected_status()
        for var_name, (sort, _) in self.variables.items():
            if sort != "Bool": #register non-boolean vars with theory solver (ints and reals)
                self.theory_solver.add_variable(var_name, sort)

    def parse_expression(self, expr, model):
        if isinstance(expr, str): #parses string expressions for z3
            if expr in self.theory_solver.get_variables():
                var = self.theory_solver.get_variables()[expr]
                if model and var in model():
                     return model()[var]
                return var
            try:
                return int(expr)
            except ValueError:
                try:
                    return float(expr)
                except ValueError:
                    raise ValueError(f"Invalid expression: {expr}")
        elif isinstance(expr, list): #parses list expressions for z3, handles all arithmetic operations
            op = expr[0]
            if op == '+':
                if len(expr) < 2:
                     raise ValueError(f"Invalid addition expression: {expr}")
                sum_expr = self.parse_expression(expr[1], model)
                for arg in expr[2:]:
                    sum_expr += self.parse_expression(arg, model)
                return sum_expr
            elif op == '-':
                if len(expr) == 2:
                    return -self.parse_expression(expr[1], model)
                elif len(expr) == 3:
                    left = self.parse_expression(expr[1], model)
                    right = self.parse_expression(expr[2], model)
                    return left - right
                else:
                    raise ValueError(f"Invalid arithmetic expression for operator {op}: {expr}")
            elif op == '*':
                if len(expr) != 3:
                    raise ValueError(f"Invalid arithmetic expression for operator {op}: {expr}")
                left = self.parse_expression(expr[1], model)
                right = self.parse_expression(expr[2], model)
                return left * right
            elif op == '/':
                 if len(expr) != 3:
                     raise ValueError(f"Invalid arithmetic expression for operator {op}: {expr}")
                 left = self.parse_expression(expr[1], model)
                 right = self.parse_expression(expr[2], model)
                 if isinstance(left, (int, float)) and isinstance(right, (int, float)):
                     return left / right
                 elif isinstance(left, (ArithRef, RatNumRef)) and isinstance(right, (ArithRef, RatNumRef)):
                     return left / right
                 else:
                      return left / right
            elif op == '=':
                if len(expr) != 3:
                    raise ValueError(f"Invalid equality expression: {expr}")
                left = self.parse_expression(expr[1], model)
                right = self.parse_expression(expr[2], model)
                return left == right # This will return a Z3 boolean expression
            else:
                raise ValueError(f"Unsupported operator in expression: {op}")
        raise ValueError(f"Invalid expression: {expr}")


    def evaluate_constraint(self, constraint, model): #Turns constraints into z3 conditions
        if not isinstance(constraint, list) or len(constraint) < 3:
            raise ValueError(f"Invalid constraint: {constraint}")
        op = constraint[0]
        left = self.parse_expression(constraint[1], model)
        right = self.parse_expression(constraint[2], model)
        if op == '=':
            return left == right
        elif op == '>':
            return left > right
        elif op == '<':
            return left < right
        elif op == '>=':
            return left >= right
        elif op == '<=':
            return left <= right
        else:
            raise ValueError(f"Unsupported operator: {op}")

    def solve(self, branching_strategy="vsids", max_conflicts=10000):
        if not self.clauses and not self.theory_constraints:
             return "SAT", {} #if there's nothing else to solve, return SAT

        if not self.clauses:
            self.theory_solver.solver.reset()
            for constraint in self.theory_constraints:
                z3_constraint = self.evaluate_constraint(constraint, {})
                self.theory_solver.add_constraint(z3_constraint)
            return self.theory_solver.check() #if there's only contraints, evaluate using theory solver

        while True: #else do cdcl loop
            result, model = solve_cdcl(self.clauses, branching_strategy, max_conflicts)
            if result == "UNSAT":
                return "UNSAT", None
            if result == "TIMEOUT":
                return "TIMEOUT", None #return Unsat or Timeout
            if result == "SAT": #if cdcl solver is sat, send model to theory solver
                self.theory_solver.solver.reset()
                for var_name, (sort, prop_id) in self.variables.items():
                    if sort == "Bool":
                        value = model.get(prop_id, False)
                        if var_name in self.theory_solver.get_variables():
                             self.theory_solver.add_constraint(self.theory_solver.get_variables()[var_name] == BoolVal(value))
                        else:
                             bool_var = self.theory_solver.add_variable(var_name, "Bool")
                             self.theory_solver.add_constraint(bool_var == BoolVal(value))

                for constraint in self.theory_constraints:
                    z3_constraint = self.evaluate_constraint(constraint, model)
                    self.theory_solver.add_constraint(z3_constraint)

                theory_result, theory_model = self.theory_solver.check()

                if theory_result == "SAT": #if theory solver returns SAT, return SAT
                    return "SAT", theory_model
                elif theory_result == "UNSAT": #if it returns UNSAT, generate conflict clause and restart loop
                    conflict_clause = []
                    for var_name, (sort, prop_id) in self.variables.items():
                        if sort == "Bool" and prop_id in model:
                            value = model[prop_id]
                            conflict_clause.append(-prop_id if value else prop_id)

                    if conflict_clause:
                        self.clauses.append(conflict_clause)
                    else:
                        return "UNSAT", None
                else:
                    return "UNKNOWN", None
            else:
                return "UNKNOWN", None


if __name__ == "__main__":

    folder_path = 'smt_file'
    output_file = os.path.join(folder_path, 'smt_results.txt')

    smt_files = [f for f in os.listdir(folder_path) if f.endswith('.smt2') or f.endswith('.smt')]

    if not smt_files:
        print(f"No .smt2 or .smt files found in '{folder_path}'. Please upload your files.")
    else:
        print(f"Found {len(smt_files)} SMT files in '{folder_path}':")
        for file_name in smt_files:
            print(f"- {file_name}")

        with open(output_file, 'w') as out:
            for file_name in smt_files:
                file_path = os.path.join(folder_path, file_name)
                print(f"\nProcessing: {file_name}")

                try:
                    with open(file_path, 'r') as f:
                        smt_content = f.read()

                    smt_solver = SMTSolver()
                    smt_solver.load_smt_file(smt_content)

                    expected = smt_solver.expected_status
                    result, model = smt_solver.solve()

                    # Print results to console
                    print(f"Expected Result: {expected}")
                    print(f"Actual Result for {file_name}: {result}")
                    if model:
                        print("Model:")
                        for var in model:
                            print(f"  {var} = {model[var]}")
                    elif result == "UNSAT":
                        print("No model for UNSAT")
                    else:
                        print("No model available (TIMEOUT or UNKNOWN)")

                    # Log results only to file
                    out.write(f"File: {file_name}\n")
                    out.write(f"Expected: {expected}\n")
                    out.write(f"Actual: {result}\n")
                    if model:
                        out.write("Model:\n")
                        for var in model:
                            out.write(f"  {var} = {model[var]}\n")
                    elif result == "UNSAT":
                        out.write("No model for UNSAT\n")
                    else:
                        out.write("No model available (TIMEOUT or UNKNOWN)\n")
                    out.write("\n")

                except Exception as e:
                    print(f"Error processing {file_name}: {e}")