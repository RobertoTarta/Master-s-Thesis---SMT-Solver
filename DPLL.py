#!/usr/bin/python3

from collections import defaultdict

def pigeonhole_principle(n):

    def var(i, j):
        return i * n + j + 1

    for i in range(1, n + 2):
        yield [var(i, j) for j in range(1, n + 1)]

    for j in range(1, n + 1):
        for i1 in range(1, n + 2):
            for i2 in range(i1 + 1, n + 2):
                yield [-var(i1, j), -var(i2, j)]

# check of empty clauses (indicates contradiction)
def contains_empty_clause(clauses):
    return any(len(clause) == 0 for clause in clauses)

# unit propagation 
def propagate_units(clauses):
    assignments = {}

    while True:
        # find all unit clauses (only one literal)
        unit_clauses = [clause for clause in clauses if len(clause) == 1]

        if not unit_clauses:
            break

        for unit in unit_clauses:
            literal = unit[0]
            var = abs(literal)
            value = literal > 0

            # check for conflicts in existing assignments
            if var in assignments and assignments[var] != value:
                return None, []

            assignments[var] = value

            # simplify clauses by removing satisfied clauses and literals
            new_clauses = []
            for clause in clauses:
                if literal in clause:
                    continue
                if -literal in clause:
                    clause = [lit for lit in clause if lit != -literal]
                new_clauses.append(clause)
            clauses = new_clauses

        if contains_empty_clause(clauses):
            return None, []

    return assignments, clauses

# perform pure literal elimination
def pure_elim(clauses):
    assignments = {}
    literal_count = defaultdict(int)

    # count occurences of each literal
    for clause in clauses:
        for literal in clause:
            literal_count[literal] += 1

    # identify pure literals
    pure_literals = [lit for lit in literal_count if -lit not in literal_count]

    for literal in pure_literals:
        var = abs(literal)
        value = literal > 0
        assignments[var] = value

        # remove clauses containing the pure literal
        clauses = [clause for clause in clauses if literal not in clause]

    return assignments, clauses

# DPLL algorithm 
def dpll(clauses, vars):
    # unit propagation
    unit_assignments, clauses = propagate_units(clauses)
    if unit_assignments is None:
        return None

    # pure literal elimination
    pure_assignments, clauses = pure_elim(clauses)

    # combine assignments
    assignments = {**unit_assignments, **pure_assignments}

    # check for contradiction or success
    if contains_empty_clause(clauses):
        return None
    if not clauses:
        return assignments  # all clauses satisfied

    # choose a variable to branch on
    literal_count = defaultdict(int)
    for clause in clauses:
        for literal in clause:
            literal_count[literal] += 1

    # heuristic: most frequent literal
    most_common_literal = max(literal_count, key=literal_count.get)
    var = abs(most_common_literal)

    # try true
    result = dpll(clauses + [[var]], vars)
    if result is not None:
        return {**assignments, **result}

    # try false
    result = dpll(clauses + [[-var]], vars)
    if result is not None:
        return {**assignments, **result}

    return None  # unsatisfiable

# output result
def output(assignments):
    if assignments is None:
        print("unsat")  # unsatisfiable
    else:
        print("sat")    # satisfiable


if __name__ == "__main__":
    
    n = 8  # number of holes / n+1 pigeons
    clauses = list(pigeonhole_principle(n))   #example 1
   #clauses = [[1, -2], [-1, 2], [2, 3]]      #example 2
   #clauses = [[1, -2, 3, -4, 5], [-1, 2, -3, 4], [2, -3, 4, -5, 6],[-2, 3, -4, 5], [1, 3, -5, 6, -7], [-1, -3, 5, -6, 7],
   #[2, 4, -6, 7], [-2, -4, 6, -7], [5, 6, -7, 8], [-5, -6, 7, -8]] #example 3
    
    vars = set(abs(lit) for clause in clauses for lit in clause)

    #show all clauses
    print("Generated Clauses:")
    for clause in clauses:
        print(clause)
 
    assignments = dpll(clauses, vars)

    output(assignments)
