"""CSP (Constraint Satisfaction Problems) problems and solvers. (Chapter 6)"""

import itertools
import random
import re
import string
from collections import defaultdict, Counter
from functools import reduce
from operator import eq, neg

from sortedcontainers import SortedSet

import search
from utils import argmin_random_tie, count, first, extend


class CSP(search.Problem):
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        variables   A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b

    In the textbook and in most mathematical definitions, the
    constraints are specified as explicit pairs of allowable values,
    but the formulation here is easier to express and more compact for
    most cases (for example, the n-Queens problem can be represented
    in O(n) space using this notation, instead of O(n^4) for the
    explicit representation). In terms of describing the CSP as a
    problem, that's all there is.

    However, the class also supports data structures and methods that help you
    solve CSPs by calling a search function on the CSP. Methods and slots are
    as follows, where the argument 'a' represents an assignment, which is a
    dict of {var:val} entries:
        assign(var, val, a)     Assign a[var] = val; do other bookkeeping
        unassign(var, a)        Do del a[var], plus other bookkeeping
        nconflicts(var, val, a) Return the number of other variables that
                                conflict with var=val
        curr_domains[var]       Slot: remaining consistent values for var
                                Used by constraint propagation routines.
    The following methods are used only by graph_search and tree_search:
        actions(state)          Return a list of actions
        result(state, action)   Return a successor of state
        goal_test(state)        Return true if all constraints satisfied
    The following are just for debugging purposes:
        nassigns                Slot: tracks the number of assignments made
        display(a)              Print a human-readable representation
    """

    def __init__(self, variables, domains, neighbors, constraints, c):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        super().__init__(())
        variables = variables or list(domains.keys())
        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.curr_domains = None
        self.nassigns = 0
        


        self.checks_sum = 0             # ένα λεξικό που χρησιμοποιείται στην ευρετική dom/wdeg (domdivwdeg)
                                        # Όλοι οι περιορισμοί του προβλήματος ξεκινούν με βάρος w = 1.
                                        # Κάθε φορά που ένας πολλαπλασιαστής οδηγεί σε αποτυχία, το βάρος του αντίστοιχου περιορισμού αυξάνεται κατά 1.
        self.constraints_weight = {}
        for key in c.keys():
            keykey_tuple = (key[0], key[1])
            self.constraints_weight[keykey_tuple] = 1

        self.last_variable = None # χρησιμοποιείται στο cbj_search για να σώσει την μεταβλητη 
        self.prev_conflict = []   # η λίστα χρησιμοποιείται στην backjump_search για να αποθηκεύσει το σύνολο των μεταβλητων που οδηγουν σε αδιεξοδο 
        self.conflict_set = {}    # map που χρησιμοποιείται στο backjump_search για να αποθηκεύσει το σύνολο των συγκρούσεων κάθε μεταβλητής
        for var in self.variables:
            self.conflict_set[var] = []

    def assign(self, var, val, assignment):
        """Add {var: val} to assignment; Discard the old value if any."""
        assignment[var] = val
        self.nassigns += 1

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):
        """Return the number of conflicts var=val has with other variables."""
        # Subclasses may implement this more efficiently
        def conflict(var2):
            return var2 in assignment and not self.constraints(var, val, var2, assignment[var2])

        return count(conflict(v) for v in self.neighbors[var])

    def display(self, assignment):
        """Show a human-readable representation of the CSP."""
        # Subclasses can print in a prettier way, or display with a GUI
        print(assignment)

    # These methods are for the tree and graph-search interface:

    def actions(self, state):
        """Return a list of applicable actions: non conflicting
        assignments to an unassigned variable."""
        if len(state) == len(self.variables):
            return []
        else:
            assignment = dict(state)
            var = first([v for v in self.variables if v not in assignment])
            return [(var, val) for val in self.domains[var]
                    if self.nconflicts(var, val, assignment) == 0]

    def result(self, state, action):
        """Perform an action and return the new state."""
        (var, val) = action
        return state + ((var, val),)

    def goal_test(self, state):
        """The goal is to assign all variables, with all constraints satisfied."""
        assignment = dict(state)
        return (len(assignment) == len(self.variables)
                and all(self.nconflicts(variables, assignment[variables], assignment) == 0
                        for variables in self.variables))

    # These are for constraint propagation

    def support_pruning(self):
        """Make sure we can prune values from domains. (We want to pay
        for this only if we use it.)"""
        if self.curr_domains is None:
            self.curr_domains = {v: list(self.domains[v]) for v in self.variables}

    def suppose(self, var, value):
        """Start accumulating inferences from assuming var=value."""
        self.support_pruning()
        removals = [(var, a) for a in self.curr_domains[var] if a != value]
        self.curr_domains[var] = [value]
        return removals

    def prune(self, var, value, removals):
        """Rule out var=value."""
        self.curr_domains[var].remove(value)
        if removals is not None:
            removals.append((var, value))

    def choices(self, var):
        """Return all values for var that aren't currently ruled out."""
        return (self.curr_domains or self.domains)[var]

    def infer_assignment(self):
        """Return the partial assignment implied by the current inferences."""
        self.support_pruning()
        return {v: self.curr_domains[v][0]
                for v in self.variables if 1 == len(self.curr_domains[v])}

    def restore(self, removals):
        """Undo a supposition and all inferences from it."""
        for B, b in removals:
            self.curr_domains[B].append(b)

    # This is for min_conflicts search

    def conflicted_vars(self, current):
        """Return a list of variables in current assignment that are in conflict"""
        return [var for var in self.variables
                if self.nconflicts(var, current[var], current) > 0]


# ______________________________________________________________________________
# Constraint Propagation with AC3


def no_arc_heuristic(csp, queue):
    return queue


def dom_j_up(csp, queue):
    return SortedSet(queue, key=lambda t: neg(len(csp.curr_domains[t[1]])))


def AC3(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    """[Figure 6.3]"""

    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        revised, checks = revise(csp, Xi, Xj, removals, checks)
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
    return True, checks  # CSP is satisfiable


def revise(csp, Xi, Xj, removals, checks=0):
    """Return true if we remove a value."""
    revised = False
    for x in csp.curr_domains[Xi][:]:
        # If Xi=x conflicts with Xj=y for every possible y, eliminate Xi=x
        # if all(not csp.constraints(Xi, x, Xj, y) for y in csp.curr_domains[Xj]):
        conflict = True
        for y in csp.curr_domains[Xj]:
            if csp.constraints(Xi, x, Xj, y):
                conflict = False
            checks += 1
            if not conflict:
                break
        if conflict:
            csp.prune(Xi, x, removals)
            revised = True
    if not csp.curr_domains[Xi]:
        csp.constraints_weight[(Xi,Xj)] += 1 # αν υπαρξει αποτυχία το βάρος του περιορισμού (Xi,Xj) αυξάνεται κατά 1

    return revised, checks


# Constraint Propagation with AC3b: an improved version
# of AC3 with double-support domain-heuristic

def AC3b(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    checks = 0
    while queue:
        (Xi, Xj) = queue.pop()
        # Si_p values are all known to be supported by Xj
        # Sj_p values are all known to be supported by Xi
        # Dj - Sj_p = Sj_u values are unknown, as yet, to be supported by Xi
        Si_p, Sj_p, Sj_u, checks = partition(csp, Xi, Xj, checks)
        if not Si_p:
            XiXj_tuple = (Xi, Xj)
            XjXi_tuple = (Xj, Xi)
            csp.constraints_weight[XiXj_tuple] += 1
            csp.constraints_weight[XjXi_tuple] += 1
            return False, checks  # CSP is inconsistent
        revised = False
        for x in set(csp.curr_domains[Xi]) - Si_p:
            csp.prune(Xi, x, removals)
            revised = True
        if revised:
            for Xk in csp.neighbors[Xi]:
                if Xk != Xj:
                    queue.add((Xk, Xi))
        if (Xj, Xi) in queue:
            if isinstance(queue, set):
                # or queue -= {(Xj, Xi)} or queue.remove((Xj, Xi))
                queue.difference_update({(Xj, Xi)})
            else:
                queue.difference_update((Xj, Xi))
            # the elements in D_j which are supported by Xi are given by the union of Sj_p with the set of those
            # elements of Sj_u which further processing will show to be supported by some vi_p in Si_p
            for vj_p in Sj_u:
                for vi_p in Si_p:
                    conflict = True
                    if csp.constraints(Xj, vj_p, Xi, vi_p):
                        conflict = False
                        Sj_p.add(vj_p)
                    checks += 1
                    if not conflict:
                        break
            revised = False
            for x in set(csp.curr_domains[Xj]) - Sj_p:
                csp.prune(Xj, x, removals)
                revised = True
            if revised:
                for Xk in csp.neighbors[Xj]:
                    if Xk != Xi:
                        queue.add((Xk, Xj))
    return True, checks  # CSP is satisfiable


def partition(csp, Xi, Xj, checks=0):
    Si_p = set()
    Sj_p = set()
    Sj_u = set(csp.curr_domains[Xj])
    for vi_u in csp.curr_domains[Xi]:
        conflict = True
        # now, in order to establish support for a value vi_u in Di it seems better to try to find a support among
        # the values in Sj_u first, because for each vj_u in Sj_u the check (vi_u, vj_u) is a double-support check
        # and it is just as likely that any vj_u in Sj_u supports vi_u than it is that any vj_p in Sj_p does...
        for vj_u in Sj_u - Sj_p:
            # double-support check
            if csp.constraints(Xi, vi_u, Xj, vj_u):
                conflict = False
                Si_p.add(vi_u)
                Sj_p.add(vj_u)
            checks += 1
            if not conflict:
                break
        # ... and only if no support can be found among the elements in Sj_u, should the elements vj_p in Sj_p be used
        # for single-support checks (vi_u, vj_p)
        if conflict:
            for vj_p in Sj_p:
                # single-support check
                if csp.constraints(Xi, vi_u, Xj, vj_p):
                    conflict = False
                    Si_p.add(vi_u)
                checks += 1
                if not conflict:
                    break
    return Si_p, Sj_p, Sj_u - Sj_p, checks


# Constraint Propagation with AC4

def AC4(csp, queue=None, removals=None, arc_heuristic=dom_j_up):
    if queue is None:
        queue = {(Xi, Xk) for Xi in csp.variables for Xk in csp.neighbors[Xi]}
    csp.support_pruning()
    queue = arc_heuristic(csp, queue)
    support_counter = Counter()
    variable_value_pairs_supported = defaultdict(set)
    unsupported_variable_value_pairs = []
    checks = 0
    # construction and initialization of support sets
    while queue:
        (Xi, Xj) = queue.pop()
        revised = False
        for x in csp.curr_domains[Xi][:]:
            for y in csp.curr_domains[Xj]:
                if csp.constraints(Xi, x, Xj, y):
                    support_counter[(Xi, x, Xj)] += 1
                    variable_value_pairs_supported[(Xj, y)].add((Xi, x))
                checks += 1
            if support_counter[(Xi, x, Xj)] == 0:
                csp.prune(Xi, x, removals)
                revised = True
                unsupported_variable_value_pairs.append((Xi, x))
        if revised:
            if not csp.curr_domains[Xi]:
                return False, checks  # CSP is inconsistent
    # propagation of removed values
    while unsupported_variable_value_pairs:
        Xj, y = unsupported_variable_value_pairs.pop()
        for Xi, x in variable_value_pairs_supported[(Xj, y)]:
            revised = False
            if x in csp.curr_domains[Xi][:]:
                support_counter[(Xi, x, Xj)] -= 1
                if support_counter[(Xi, x, Xj)] == 0:
                    csp.prune(Xi, x, removals)
                    revised = True
                    unsupported_variable_value_pairs.append((Xi, x))
            if revised:
                if not csp.curr_domains[Xi]:
                    return False, checks  # CSP is inconsistent
    return True, checks  # CSP is satisfiable


# ______________________________________________________________________________
# Variable ordering


def first_unassigned_variable(assignment, csp):
    """The default variable order."""
    return first([var for var in csp.variables if var not in assignment])


def domdeg(assignment, csp): # η ευρετική μέθοδος dom/wdeg επιλέγει τη μεταβλητή με τη χαμηλότερη αναλογία dom/wdeg
                            # σε κάθε μεταβλητή δινεται ένας βαθμός ο οποίος είναι το άθροισμα των βαρών όλων των περιορισμών στους οποίους συμμετέχει
    if csp.curr_domains == None:
        return first_unassigned_variable(assignment, csp)

    min_var = float('inf')
    min_value = float('inf')
    
    variables_sum = {} #αποθηκευω τον βαθμό για κάθε μεταβλητή
    for var in csp.variables:

        if var in assignment:
            continue

        variables_sum[var] = 0 # υπολογισμός του βαθμού της μεταβλητής var
        for nei in csp.neighbors[var]:
            if nei not in assignment:
                var_nei_tuple = (var, nei)
                variables_sum[var] += csp.constraints_weight[var_nei_tuple]

        if variables_sum[var] == 0:
            continue
        
        curr_domains_length = len(csp.curr_domains[var]) # για τη μεταβλητή var παιρνω τον αριθμό των διαθέσιμων τιμών από τον τομέα
        if  min_value > curr_domains_length / variables_sum[var]: # βρισκω τη μεταβλητή με το μικρότερο  dom / wdeg
            min_value = (curr_domains_length / variables_sum[var])
            min_var = var

    if min_var != float('inf'):
        return min_var
    else:
        return first_unassigned_variable(assignment, csp)


def mrv(assignment, csp):
    """Minimum-remaining-values heuristic."""
    return argmin_random_tie([v for v in csp.variables if v not in assignment],
                             key=lambda var: num_legal_values(csp, var, assignment))


def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0 for val in csp.domains[var])


# Value ordering


def unordered_domain_values(var, assignment, csp):
    """The default value order."""
    return csp.choices(var)


def lcv(var, assignment, csp):
    """Least-constraining-values heuristic."""
    return sorted(csp.choices(var), key=lambda val: csp.nconflicts(var, val, assignment))


# Inference


def no_inference(csp, var, value, assignment, removals):
    return True


def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    csp.support_pruning()
    check = 0
    for B in csp.neighbors[var]:

        if B not in assignment:
            for b in csp.curr_domains[B][:]:

                check += 1
                if not csp.constraints(var, value, B, b):
                    csp.prune(B, b, removals)
            if not csp.curr_domains[B]:
                Bvar_tuple = (B, var)
                csp.constraints_weight[Bvar_tuple] += 1 #αν υπαρξει αποτυχια η σταθερα βαρους (Β, var) αυξανεται κατα 1

                return False, check
            
    return True, check


def mac(csp, var, value, assignment, removals, constraint_propagation=AC3):
    """Maintain arc consistency."""
    return constraint_propagation(csp, {(X, var) for X in csp.neighbors[var]}, removals)

#------------------ Backtracking ------------------
def backtracking_search(csp, select_unassigned_variable = domdeg, order_domain_values = lcv, inference = mac):
    """[Figure 6.5]"""
    
    def backtrack(assignment):
        if len(assignment) == len(csp.variables):
            return assignment
        
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):

            if 0 == csp.nconflicts(var, value, assignment):
                csp.assign(var, value, assignment)
                removals = csp.suppose(var, value)

                inference_return = inference(csp, var, value, assignment, removals)
                condition = inference_return[0]
                check = inference_return[1]

                csp.checks_sum += check
                if condition:
                    result = backtrack(assignment)
                    if result is not None:
                        return result
                    
                csp.restore(removals)

        csp.unassign(var, assignment)

        return None

    result = backtrack({})
    assert result is None or csp.goal_test(result)
    return result,csp.checks_sum


def backjump_search(csp, select_unassigned_variable = domdeg, order_domain_values = lcv, inference = forward_checking):

    def restore_conflicts(var, csp): #ενημέρωση του συνόλου των συγκρούσεων κάθε μεταβλητής
                                    #προσθετω τη νέα μεταβλητή η οποία έχει μπαινει σε οποιο σύνολο δεν εχει συνεπεια
        for v in csp.variables:
            if var in csp.neighbors[v]:
                if var not in csp.conflict_set[v]: 
                    csp.conflict_set[v].append(var)
        return csp.conflict_set

    def merge_func(var, assigned_vars, csp):

        for v in csp.variables:

            tmp = []
            if v == var:
                csp.conflict_set[v] += csp.prev_conflict #συγχονευση μελων 

            for as_var in assigned_vars: #διαγραφω 
                if as_var in csp.conflict_set[v]:
                    tmp.append(as_var)

            csp.conflict_set[v] = tmp

        return csp.conflict_set

    def backjump(assignment):

        if len(assignment) == len(csp.variables):
            return assignment
        
        var = select_unassigned_variable(assignment, csp)
        for value in order_domain_values(var, assignment, csp):

            if csp.nconflicts(var, value, assignment) == 0: 

                csp.assign(var, value, assignment)
                assigned_vars.append(var)
                csp.conflict_set = restore_conflicts(var, csp)
                ejections = csp.suppose(var, value)
                cond, check = inference(csp, var, value, assignment, ejections)
                csp.checks_sum += check
                if cond:
                    result = backjump(assignment)
                    if result is not None:
                        return result
                csp.restore(ejections)

            
            if csp.last_variable != None and var in csp.conflict_set[csp.last_variable]: # έλεγχος αν η τελευταία (προηγούμενη) μεταβλητή (last_variable) είχε αδιέξοδο
                                                                                        # και αν η τρέχουσα μεταβλητή ανήκει στο σύνολο των συγκρούσεων
                                                                                        # προσπαθω να βρω τη μεταβλητή στο σύνολο των συγκρούσεων της μεταβλητής που βρέθηκε σε αδιέξοδο 
                                                                                        #η οποία ανήκει βαθύτερα στο δέντρο αναζήτησης
                                                                                        # όταν βρεθεί αυτή η μεταβλητή κανω merge_func το συνολο των συγκρούσεων
                
                csp.last_variable = None #αν το εχω βρει συγχωνευω τα σύνολα συγκρούσεων 
                                        #και προσθετω το σύνολο συγκρούσεων της αδιέξοδης μεταβλητής στο σύνολο συγκρούσεων της τρέχουσας μεταβλητής
                csp.conflict_set = merge_func(var, assigned_vars, csp)
            csp.unassign(var, assignment)
            if var in assigned_vars:
                del assigned_vars[assigned_vars.index(var)]
            if csp.last_variable != None:
                return None

        # at the last_variable, I save the variable which hasn't other values to test (dead-end),
        # also I save the corresponding set of conflicts
        csp.last_variable = var
        csp.prev_conflict = csp.conflict_set[csp.last_variable]
        return None

    assigned_vars = []
    result = backjump({})
    assert result is None or csp.goal_test(result)
    return result,csp.checks_sum

# ______________________________________________________________________________
# Min-conflicts Hill Climbing search for CSPs


def min_conflicts(csp, max_steps=100000):
    """Solve a CSP by stochastic Hill Climbing on the number of conflicts."""
    # Generate a complete assignment for all variables (probably with conflicts)
    csp.current = current = {}
    for var in csp.variables:
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    # Now repeatedly choose a random conflicted variable and change it
    for i in range(max_steps):
        conflicted = csp.conflicted_vars(current)
        if not conflicted:
            return current
        var = random.choice(conflicted)
        val = min_conflicts_value(csp, var, current)
        csp.assign(var, val, current)
    return None, csp.checks_sum


def min_conflicts_value(csp, var, current):
    """Return the value that will give var the least number of conflicts.
    If there is a tie, choose at random."""
    return argmin_random_tie(csp.domains[var], key=lambda val: csp.nconflicts(var, val, current))