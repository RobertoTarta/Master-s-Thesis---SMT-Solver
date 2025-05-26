from collections import defaultdict
import random

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
        for clause in clauses + learned_clauses: #for each clause
            unassigned = [lit for lit in clause if lit not in assignments and -lit not in assignments] #gather all unassigned literals
            assigned_true = any(assignments.get(lit, False) for lit in clause)  #check if any literal in clause is true
            if assigned_true: #if so, proceed to next clause
                continue
            if not unassigned and not assigned_true:#all lits assigned and none true, returns a Conflict
                return clause
            if len(unassigned) == 1:#one lit is unassigned
                lit = unassigned[0]
                assignments[lit] = True #make it true
                decision_stack.append((lit, level, "implied")) # save in decision stack, the literal, the decision level and that it was implied
                unit_found = True
                break #loop back
        if not unit_found:
            return None #no conflicts found and no more unit clauses

def analyze_conflict(conflict_clause, assignments, decision_stack, level, vsids_scores=None):
    
    if level == 0: #if conflict found at root level (decision lvl 0), return UNSAT
        return None, -1

    conflict_vars = set(abs(lit) for lit in conflict_clause) #store conflicting variables
    relevant_decisions = set()                               #store decisions that led to conflict
    for lit, lvl, reason in reversed(decision_stack):   #go through decisions from recent to old
        if lvl > level:
            continue
        if reason == "decision":  #check if decision implied the conflict
            if abs(lit) in conflict_vars or any(abs(l) in conflict_vars for l, l_lvl, r in decision_stack if l_lvl == lvl and r == "implied"):
                relevant_decisions.add(lit) #if so, store in relevant decisions set

    learned_clause = [] #initialize new set, if any new clauses are to be learned
    for lit in relevant_decisions: #for each relevant decision
        negated_lit = -lit if assignments.get(lit, False) else lit #negate it
        learned_clause.append(negated_lit) #store in learned clauses
        if vsids_scores is not None: #for VSIDS, increase score for literal
            vsids_scores[abs(lit)] += 1

    if not learned_clause:
        if not decision_stack: #if decision stack is empty (meaning no decisions can be made) and nothing is learned
            return None, -1  # return unsatisfiable
        last_decision = next((lit for lit, lvl, r in reversed(decision_stack) if r == "decision" and lvl == level), None)
        if last_decision: #find last decision at current level, when no relevant decisions are found leading to conflict
            learned_clause = [-last_decision if assignments.get(last_decision, False) else last_decision] #negate it

    levels = sorted([lvl for lit, lvl, r in decision_stack if r == "decision" and (lit in relevant_decisions or lit in [abs(l) if l > 0 else -l for l in learned_clause])], reverse=True)
    backtrack_level = levels[1] if len(levels) > 1 else 0 #backtrack to 2nd highest level

    return learned_clause, backtrack_level #return new clause and backtrack level

def backtrack(decision_stack, assignments, level):
    
    decision_stack[:] = [(lit, lvl, reason) for lit, lvl, reason in decision_stack if lvl <= level] #save decisions up to backtrack level
    assignments.clear()
    for lit, _, _ in decision_stack:
        assignments[lit] = True

def decide(clauses, assignments, decision_stack, level, strategy="first", vsids_scores=None):
    
    unassigned_vars = set() #stores unassigned, as its a set, prevents duplicates
    var_count = defaultdict(int) #counts frequency of a literal
    for clause in clauses: #iterates all clauses in formula
        for lit in clause: #iterates all literals in clause
            if lit not in assignments and -lit not in assignments: #if lit or negation unassigned
                unassigned_vars.add(lit) #add to unassigned
                var_count[lit] += 1 #increase frequency for literal
    if not unassigned_vars: #if no more unassigned found
        return False, level #return that all vars have been assigned
    level += 1 #increase decision level
               #decision strategies:
    if strategy == "first":
        lit = min(unassigned_vars)
    elif strategy == "random":
        lit = random.choice(list(unassigned_vars))
    elif strategy == "frequent":
        lit = max(var_count.items(), key=lambda x: x[1])[0]
    elif strategy == "vsids" and vsids_scores:
        lit = max(unassigned_vars, key=lambda l: vsids_scores.get(abs(l), 0))
    else:
        lit = min(unassigned_vars)#chooses smallest variable (preferably negatives)
    assignments[lit] = True
    decision_stack.append((lit, level, "decision")) #adds decision to stack
    return True, level #returns that a lit has been assigned and new decision level

def solve_cdcl(clauses, branching_strategy="first", max_conflicts=10000):
    
    assignments = {} #(lit=true),ex:(-1=True)
    decision_stack = [] #(lit,lvl,reason),ex: (-x1,2,"decision")
    learned_clauses = [] #(clause),ex: [-1,2,-3]
    level = 0
    vsids_scores = defaultdict(float) if branching_strategy == "vsids" else None #VSIDS Data initialization
    conflict_count = 0
    decay_factor = 0.95
    decay_interval = 10

    if vsids_scores:
        for clause in clauses:
            for lit in clause:
                vsids_scores[abs(lit)] += 0.1 #Start VSIDS scores with a small value

    while conflict_count < max_conflicts: #main loop
        conflict = unit_propagation(clauses, learned_clauses, assignments, decision_stack, level) #does propagation
        if conflict is not None: #if conflict
            conflict_count += 1
            learned_clause, backtrack_level = analyze_conflict(conflict, assignments, decision_stack, level, vsids_scores) #learn new clause
            if backtrack_level < 0:
                return "UNSAT", None
            learned_clauses.append(learned_clause)
            backtrack(decision_stack, assignments, backtrack_level) #backtrack
            level = backtrack_level
            if vsids_scores and conflict_count % decay_interval == 0: #decay vsids score
                for var in vsids_scores:
                    vsids_scores[var] *= decay_factor
        else:
            decided, new_level = decide(clauses, assignments, decision_stack, level, branching_strategy, vsids_scores) #decide new literal
            if not decided:
                max_var = max(abs(lit) for clause in clauses for lit in clause)
                #builds the solution
                solution = {i: assignments.get(i, False) or not assignments.get(-i, False) for i in range(1, max_var + 1)}
                return "SAT", solution
            level = new_level
    return "TIMEOUT", None #too many loops occured without reaching a solution (limited to 10000)

if __name__ == "__main__":
    
    # Test 1: Satisfiable
    clauses = [[1, -2], [-1, 2], [2, 3]]
    print("Test 1: Satisfiable")
    result, solution = solve_cdcl(clauses, branching_strategy="vsids")
    print(f"Result: {result}")
    if solution:
        print(f"Solution: {solution}")

    # Test 2: Unsatisfiable
    n=11
    clauses = list(pigeonhole_principle(n))
    print("\nTest 2: Unsatisfiable")
    result, solution = solve_cdcl(clauses, branching_strategy="vsids")
    print(f"Result: {result}")

    # Test 3: Satisfiable
    clauses =    [
        [1, -2, 3, -4, 5], [-1, 2, -3, 4], [2, -3, 4, -5, 6],
        [-2, 3, -4, 5], [1, 3, -5, 6, -7], [-1, -3, 5, -6, 7],
        [2, 4, -6, 7], [-2, -4, 6, -7], [5, 6, -7, 8], [-5, -6, 7, -8]
    ]

    print("\nTest 3: Satisfiable")
    result, solution = solve_cdcl(clauses, branching_strategy="vsids")
    print(f"Result: {result}")
    if solution:
        print(f"Solution: {solution}")