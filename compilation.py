# Converts a tight probababilistic logic program
# into a weighted CNF model counting problem in
# DIMACS format
#
# The program expects the logic program to have a simple
# format where each rule is in a different line
# and contains only normal rules and probabilistic facts.
# For the moment, the program does not encode the probabilities
# into the generated CNF. A possibility would be to encode it
# as a weighted CNF. The order of appearance of atoms in the program
# is preserved in the output, so that if probabilistic facts appear at
# the top, then they will be assigned the lowest indices in
# the DIMACS format.

import os
from dataclasses import dataclass
from sys import exception
from typing import ClassVar
import re
import pysdd.sdd as sdd
import time

@dataclass
class Atom:
    "Propositional atom"
    id: int
    txt: str = ""
    total: ClassVar[int] = 0
    #relation: int
    #tuple: list[int]

    def __init__(self, id:int, txt:str=""):
        if id >= 0:
            self.id = id
        else:
            self.id = Atom.total
        self.txt = txt
        Atom.total += 1

    def __str__(self) -> str:
        if self.txt == '':
            return f"a{self.id}"
        else: return f"{self.txt}#{self.id+1}"

    def __hash__(self) -> int:
        return self.id

@dataclass
class NormalRule:
    "Represents a normal rule"
    head: Atom
    pbody: list[Atom]
    nbody: list[Atom]

    def __str__(self) -> str:
        return f"{self.head}:-" + ','.join([str(a) for a in self.pbody] + [ "not " + str(a) for a in self.nbody ]) + "."

@dataclass
class DisjunctiveRule:
    "Represents a disjunctive rule"
    head: list[Atom]
    pbody: list[Atom]
    nbody: list[Atom]

    def __str__(self) -> str:
        return ';'.join([str(a) for a in self.head]) + ":-" + ','.join([str(a) for a in self.pbody] + [ "not " + str(a) for a in self.nbody ]) + "."

@dataclass
class ChoiceRule:
    "Represents a choice rule"
    head: list[Atom]
    pbody: list[Atom]
    nbody: list[Atom]
    lower: int
    upper: int

    def __str__(self) -> str:
        return f"{self.lower}" + '{' +  ';'.join([str(a) for a in self.head]) + '}' + f"{self.upper}" + ':-' + ','.join([str(a) for a in self.pbody] + [ "not " + str(a) for a in self.nbody ]) + "."

@dataclass
class PFact:
    "Probabilistic Fact"
    head: Atom
    prob: float

    def __str__(self) -> str:
        return f"{self.prob}::{self.head}."

@dataclass
class AnnotatedDisjunction:
    "Annotated Disjunction"
    head: list[Atom]
    prob: list[float]

    def __str__(self) -> str:
        return ';'.join(f"{p}::{a}" for a,p in zip(self.head,self.prob)) + '.'

@dataclass
class Program:
    "Represents a probabilistic logic program"
    pfacts: list # probabilistic facts
    ads: list # annotated disjunctions
    nrules: list[NormalRule] # normal rules
    drules: list[DisjunctiveRule] # disjunctive rules
    crules: list[ChoiceRule] # choice rules
    #num_atoms: int = -1

    def __init__(self):
        " Creates an empty program "
        self.pfacts = []
        self.ads = []
        self.nrules = []
        self.drules = []
        self.crules = []

    def __str__(self) -> str:
        return '\n'.join(['c ' + str(r) for r in self.pfacts + self.ads + self.nrules + self.drules + self.crules])

    def shift(self):
        ''''
        Apply shifting to disjunctive rules (Ben-Eliyahu and Dechter, 1994),
        assumes program is head cycle free.
        '''
        #print("normalizing")
        for r in self.drules:
            # print("->", r)
            for a in r.head:
                ext = [b for b in r.head if b.id != a.id]
                r2 = NormalRule(a, r.pbody, r.nbody + ext)
                self.nrules.append(r2)
        self.drules = []

    def rewriteADs(self):
        ''' Rewrite annotated disjunctions as probabilistic facts + normal rules
        and remove them from program '''
        for r,rule in enumerate(self.ads):
            cum = 0.0
            for i in range(len(rule.head)-1):
                p,a = rule.prob[i],rule.head[i]
                aux = Atom(-1,f"_AUX_{r}_" + a.txt)
                self.pfacts.append( PFact(aux,p/(1-cum)) )
                cum += p
                self.nrules.append( NormalRule(a,[aux],rule.head[:i]) )
            self.nrules.append( NormalRule(rule.head[-1],[],rule.head[:-1]) )
        self.ads = []

    def toCNF(self, add_comments=False) -> str:
        '''Converts to CNF.
        Builds the Clark completion of program using m auxiliary variables, where m
        is the number of rules. Preserves model counting.

        Assumptions:
            - program is normal and tight (positive dependency graph is acyclic)
            - atoms in probabilistic facts do not unify with any rule head
        '''
        cnf = "" # output string
        # We first verify if program is in expected form
        pids = set() # ids of probabilistic atoms
        for f in P.pfacts:
            pids.add(f.head.id)
            # add literal weights using MC2023 format
            if add_comments:
                cnf += f"c Prob({f.head}) = {f.prob}\n"
            cnf += f"w {f.head.id+1} {f.prob:.9f} 0\nw -{f.head.id+1} {1.0-f.prob:.9f} 0\n"
            # MC2021 format slightly differs from this: https://mccompetition.org/assets/files/2021/competition2021.pdf
            # it uses 'p weight [-]id prob 0'
        lids = set() # ids of non-probabilistic atoms
        for r in P.nrules:
            if r.head.id in pids:
                raise Exception("Rule head unified with probabilistic fact. Aborting...")
            lids.add(r.head.id)
            for a in r.pbody:
                if a.id not in pids:
                    lids.add(a.id)
            for a in r.nbody:
                if a.id not in pids:
                    lids.add(a.id)
        eids = set() # ids of atoms in exactly-one clauses
        for r in P.crules:
            for a in r.head:
                if a.id in pids:
                    raise Exception("Rule head unified with probabilistic fact. Aborting...")
                lids.add(a.id)
                eids.add(a.id)
        if len(pids.intersection(lids)) != 0:
            raise Exception("Non-disjoint p-atoms and l-atoms lists. Aborting...")
        ids = pids.union(lids)
        imin, imax = min(ids), max(ids)
        if len(ids) != imax-imin+1:
            raise Exception("Atom indices are not normalized! Aborting...")
        num_rules = 0 # len(P.rules)
        num_clauses = 0
        # We create auxiliary variables r#id to represent the body of each normal rule
        headCompletion = {} # head atom => rule ids
        facts = set()
        # rule id = #atoms + position of rule
        rid = len(ids)
        if add_comments:
            cnf += 'c Support Rule Clauses\n'
        for i,r in enumerate(P.nrules):
            # Constraints are encoded directly
            if r.head.txt == '_FALSE':
                if add_comments:
                    cnf += f"c {r}\n"
                for a in r.pbody:
                    cnf += f"-{a.id+1} "
                for a in r.nbody:
                    cnf += f"{a.id+1} "
                cnf += "0\n"
                num_clauses += 1
            elif len(r.pbody) == 0 and len(r.nbody) == 0:
                # FACT
                if add_comments:
                    cnf += f"c FACT: {r.head}\n"
                facts.add(r.head.id)
                cnf += f"{r.head.id+1} 0\n"
                num_clauses += 1
            else:
                # Id of auxiliary variable
                rid += 1
                if add_comments:
                    sep = ''
                    if len(r.pbody) > 0 and len(r.nbody) > 0:
                        sep = ' ^ '
                    cnf += f"c r{rid-len(ids)}#{rid} <=> {' ^ '.join(str(a) for a in r.pbody)}{sep}{' ^ '.join('-' + str(a) for a in r.nbody)}\n"
                # list rules with same head
                if r.head in headCompletion:
                    headCompletion[r.head].append(rid)
                else:
                    headCompletion[r.head] = [rid]
                # rule => head
                if add_comments:
                    cnf += f"c r{rid-len(ids)}#{rid} => {r.head}\n"
                cnf += f"-{rid} {r.head.id+1} 0\n"
                num_clauses += 1
                # rule => body
                for a in r.pbody:
                    if add_comments:
                        cnf += f"c r{rid-len(ids)}#{rid} => {a}\n"
                    cnf += f"-{rid} {a.id+1} 0\n" # rule => atom
                    num_clauses += 1
                for a in r.nbody:
                    if add_comments:
                        cnf += f"c r{rid-len(ids)}#{rid} => -{a}\n"
                    cnf += f"-{rid} -{a.id+1} 0\n" # rule => neg atom
                    num_clauses += 1
                # body => rule
                if add_comments:
                    cnf += f"c {' ^ '.join([str(b) for b in r.pbody]+['-'+str(b) for b in r.nbody])} => r{rid-len(ids)}#{rid}\n"
                cnf += f"{rid} "
                if len(r.pbody) > 0:
                    cnf += ' '.join([f"-{a.id+1}" for a in r.pbody]) + " "
                if len(r.nbody) > 0:
                    cnf += ' '.join([f"{a.id+1}" for a in r.nbody]) + " "
                cnf += "0\n"
                num_clauses += 1
                num_rules += 1
        if add_comments:
            cnf += 'c Completion\n'
        for a in headCompletion:
            # head => union of rules
            if add_comments:
                cnf += f"c {a} => " + ' v '.join([ f"r{rid-len(ids)}#{rid}" for rid in headCompletion[a]]) + "\n"
            cnf += f"-{a.id+1} " + ' '.join([str(rid) for rid in headCompletion[a]]) + " 0\n"
            num_clauses += 1
        # force logical atoms that do not appear in heads to be false
        for a in lids.difference(set(b.id for b in headCompletion)).difference(facts).difference(eids):
            if add_comments:
                cnf += f"c #{a+1} must be false\n"
            cnf += f"-{a+1} 0\n"
            num_clauses += 1
        # Process Exactly One Contraints\
        num_eclauses = 0
        for r in P.crules:
            if r.lower == 1 and r.upper == 1 and len(r.pbody) == 0 and len(r.nbody) == 0:
                if add_comments:
                    cnf += f"c Exactly-One Clause {r}\n"
                cnf += ' '.join([f"{a.id+1}" for a in r.head]) + " 0\n"
                num_eclauses += 1
        header = f"p wcnf {len(ids)+num_rules} {num_clauses+num_eclauses}\n"
        if num_eclauses > 0:
            header += f"eclauses {num_eclauses}\n"
        return header + cnf


class Parser:

    def parsePFact(text:str, trl:dict[str,Atom]) -> PFact:
        "Builds probabilistic fact from textual representation and dictionary of text-atom mappings"
        p,a = text.split("::")
        p,a = p.strip(),a.strip()
        if a[-1] != '.':
            raise Exception("Syntax Error: probabilistic fact does not end with '.'")
        a_txt = a[:-1]
        prob = float(p)
        if a_txt in trl:
            atom = trl[a_txt]
        else: # first time atom is declared
            atom = Atom(len(trl), a_txt)
            trl[a_txt] = atom
        return PFact(atom,prob)

    def parseAD(text:str, trl:dict[str,Atom]) -> PFact:
        "Builds annotated disjunction  from textual representation and dictionary of text-atom mappings"
        atoms = []
        probs = []
        heads = text.split(';')
        for atom in heads:
            p,a = atom.split("::")
            p,a = float(p.strip()),a.strip()
            if a[-1] == '.':
                a = a[:-1]
            prob = float(p)
            if a in trl:
                atom = trl[a]
            else: # first time atom is declared
                atom = Atom(len(trl), a)
                trl[a] = atom
            atoms.append(atom)
            probs.append(p)
        return AnnotatedDisjunction(atoms,probs)

    _regex_atom = r'[a-z][0-9A-z_]*([(][^)]+[)])?'
    _regex_skip = r'[ \t]+'
    _regex_and = r','
    _regex_or = r';'
    _regex_normalrule = f"(?P<HEAD>{_regex_atom})?({_regex_skip})?(:-){_regex_skip}(?P<BODY>[^.]*)[.]"
    _regex_rule = f"(?P<HEAD>[^.]*)(:-){_regex_skip}(?P<BODY>[^.]*)[.]"
    #_regex_rule = f"(?P<HEAD>{_regex_atom})?{_regex_skip}(:-){_regex_skip}(?P<BODY>[^.]*)[.]"
    #_regex_body = f"(?P<NLIT>not[ ]+{_regex_atom})|(?P<PLIT>{_regex_atom})|(?P<SKIP>[ \t,]+)"
    _regex_head = f"(?P<PLIT>{_regex_atom})|{_regex_or}|{_regex_skip}"
    _regex_body = f"(?P<NLIT>not[ ]+{_regex_atom})|(?P<PLIT>{_regex_atom})|{_regex_and}|{_regex_skip}"

    def parseRule(text:str, trl:dict[str,Atom]) -> DisjunctiveRule:
        "Builds rule from textual representation and dictionary of text-atom mappings"
        #mo = re.search(Parser._regex_normalrule, text)
        mo = re.search(Parser._regex_rule, text)
        if mo is None:
            raise Exception("Could not parse rule:", text)
        # Parse head
        head_txt = mo.group('HEAD')
        head = []
        for atom in re.finditer(Parser._regex_head, head_txt):
            kind = atom.lastgroup
            value = atom.group()
            if kind == 'PLIT':
                if value in trl:
                    head_atom = trl[value]
                else: # first time atom is seen
                    head_atom = Atom(len(trl), value)
                    trl[value] = head_atom
                head.append(head_atom)
        if len(head) == 0: # constraint
            if "_FALSE" in trl:
                false_atom = trl["_FALSE"]
            else: # first time atom is seen
                false_atom = Atom(len(trl), "_FALSE")
                trl[false_atom] = false_atom
            head.append(false_atom)
        # Now parse body
        body = mo.group('BODY')
        pbody, nbody = [], []
        # print(head, '<-', body)
        for mo in re.finditer(Parser._regex_body, body):
            kind = mo.lastgroup
            value = mo.group()
            atom_str = None
            pos = False
            if kind == 'PLIT':
                atom_str = value
                pos = True
            elif kind == 'NLIT':
                atom_str = value[4:]
            # print(f'{mo.start():2d}-{mo.end():2d}:', kind, value)
            if atom_str is not None:
                if atom_str in trl:
                    atom = trl[atom_str]
                else: # first time atom is declared
                    atom = Atom(len(trl), atom_str)
                    trl[atom_str] = atom
                if pos: pbody.append(atom)
                else: nbody.append(atom)
        if len(head) == 1:
            return NormalRule(head[0],pbody,nbody)
        else:
            return DisjunctiveRule(head,pbody,nbody)

    _regex_choice_head = f"(?P<ATOM>{_regex_atom})|{_regex_or}|{_regex_skip}"
    _regex_choice = '{(?P<HEAD>[^}]+)}'+f"{_regex_skip}={_regex_skip}1{_regex_skip}."
    #_regex_choice = '{|'+ f"(?P<ATOM>{_regex_atom})|{_regex_skip}|;" + '|}' + f"{_regex_skip}" + '=' + f"{_regex_skip}" + '1' + f"{_regex_skip}" + '.'

    def parseChoiceRule(text:str, trl:dict[str,Atom]) -> ChoiceRule:
        # For now, handles only rule of form {a,b,...} = 1.
        mo = re.search(Parser._regex_choice, text)
        if mo is None:
            raise Exception("Could not parse rule:", text)
        head = []
        #print(head)
        for mo in re.finditer(Parser._regex_atom, mo.group('HEAD')):
            atom_str = mo.group()
            #print(f'{mo.start():2d}-{mo.end():2d}:', atom_str)
            if atom_str in trl:
                atom = trl[atom_str]
            else: # first time atom is declared
                atom = Atom(len(trl), atom_str)
                trl[atom_str] = atom
            head.append(atom)
        return ChoiceRule(head,[],[],1,1)

    def parse(file_path:str, debug = False):
        "Parse a program from text file -- Assumes one rule/probabilistic fact per line"
        txt2atom = {} # cache of atoms in the program
        P = Program() # empty program
        i = 0
        with open(file_path) as program_file:
            for line in program_file:
                line = line.strip()
                if debug:
                    i = i + 1
                    print(f"#{i}", line)
                if len(line) == 0 or line[0] == "%" or line[0] == "#":
                    # ignore comment lines and directives
                    continue
                line = line + " "
                for rule in line.split('. '):
                    rule = rule.strip() + '.'
                    if rule.find("::") >= 0:
                        if rule.find(";") >= 0: # annotated disjunction
                            P.ads.append(Parser.parseAD(rule,txt2atom))
                        else:
                            P.pfacts.append(Parser.parsePFact(rule,txt2atom))
                    elif rule.find(":-") >= 0:
                        r = Parser.parseRule(rule,txt2atom)
                        if type(r) is NormalRule:
                            P.nrules.append(r)
                        else:
                            P.drules.append(r)
                    elif rule.find("{") >= 0:
                        P.crules.append(Parser.parseChoiceRule(rule,txt2atom))
                    else:
                        if debug:
                            print('c Unknown syntax, rule ignored')
                        continue
        return P, text2atom


if __name__ == "__main__":
    import sys
    # Parse options
    file_path = None
    add_comments = False
    generate_nnf = False
    order_heuristic = False
    for arg in sys.argv[1:]:
        if arg == '-c':
            add_comments = True
        elif arg == '-n':
            generate_nnf = True
        elif arg == '-o':
            order_heuristic = True
        elif file_path is None:
            file_path = arg
    if file_path is None:
        print(f"Usage: {sys.argv[0]} file_path [-c] [-n]")
        print(" -c: Add comments to output")
        print(" -n: Parse but do not produce CNF (for debugging)")
        exit(1)
    try:
        P, text2atom = Parser.parse(file_path)
        filename = file_path[:-5]
        if len(P.drules) > 0:
            print("c Applied Shifting to Disjunctive Rules")
            P.shift()
        if len(P.ads) > 0:
            print("c Translated Annotated Disjunctions")
            P.rewriteADs()
        if add_comments:
            print(f"c Input: {file_path}")
            print("c ---")
            print(P)
            print("c ---")
        if generate_nnf:
            cnf = P.toCNF(add_comments=add_comments)
            with open(filename + '.cnf', 'w') as f:
                print(cnf, file=f)

        num_atoms = len(text2atom)
        # Graph representation
        # Each node is an atom
        nodes = [i for i in range(num_atoms)]
        # An edge from i to j means that atom i is in the body of a rule with head j
        adjacencies = [[] for _ in range(num_atoms)]
        # Flag for each atom that indicates if it is a source atom
        is_source = [True for _ in range(num_atoms)]
        # Group rules by head
        rules_by_head = [(rule.head.id, [], []) for rule in P.nrules]
        for rule in P.nrules:
            head = rule.head.id
            is_source[head] = False
            pbody = rule.pbody
            nbody = rule.nbody
            for atom in pbody + nbody:
                adjacencies[atom.id].append(head)
            rules_by_head[head][1].append(pbody)
            rules_by_head[head][2].append(nbody)

        start = time.time()
        order = [i for i in range(num_atoms)]
        if order_heuristic:
            # If a node has no incoming edges, it is a source
            sources = [atom for atom, flag in enumerate(is_source) if flag]
            # Compute the number of descendants of each node
            descendants = [0 for _ in range(num_atoms)]
            for source in sources:
                visited = [False for _ in range(num_atoms)]
                stack = [source]
                # BFS to count descendants
                # The stack is used to avoid recursion
                # The visited list is used to avoid visiting the same node multiple times
                # The descendants list is used to store the number of descendants of each node
                while stack:
                    node = stack.pop()
                    visited[node] = True
                    for neighbor in adjacencies[node]:
                        if not visited[neighbor]:
                            stack.append(neighbor)
                            descendants[node] += 1
            # Sort sources by number of descendants
            sources.sort(key=lambda x: descendants[x])
            # The order is the BFS of the sources
            visited = [False for _ in range(num_atoms)]
            order = []
            for source in sources:
                stack = [source]
                while stack:
                    node = stack.pop()
                    if not visited[node]:
                        visited[node] = True
                        order.append(node)
                        for neighbor in adjacencies[node]:
                            stack.append(neighbor)
            # Throw an error if the order is incomplete
            if len(order) != num_atoms:
                raise Exception("Order heuristic failed: number of nodes in order is different from number of atoms")

        # Create SDD manager following the previously obtained order
        vtree = sdd.Vtree(var_count=num_atoms, var_order=order, vtree_type='balanced')
        sdd_manager = sdd.SddManager.from_vtree(vtree)
        vars = sdd_manager.vars

        # Build SDD
        program_sdd = sdd_manager.true()
        for (head, pbodies, nbodies) in rules_by_head:
            head_sdd = vars[head]
            # Disjunction of all bodies
            bodies_sdd = sdd_manager.false()
            for pbody, nbody in zip(pbodies, nbodies):
                # Conjunction of all atoms in the body
                body_sdd = sdd_manager.true()
                for atom in pbody:
                    body_sdd = body_sdd & vars[atom.id]
                for atom in nbody:
                    body_sdd = body_sdd & ~vars[atom.id]
                bodies_sdd = bodies_sdd | body_sdd
            # Iff between head and bodies (head only occurs if one of the bodies is true)
            program_sdd = program_sdd & (~head_sdd | bodies_sdd) & (head_sdd | ~bodies_sdd)

        size = program_sdd.size()
        mc = program_sdd.model_count()
        compilation_time = start - time.time()
        compression_rate = mc / size
        print(f"{filename} {size} {compilation_time} {mc} {compression_rate}")

    except FileNotFoundError:
        print(f"File {file_path} not found!")
    #txt2atom = {}
    #a = Atom(1)
    #pa = PFact(a, 0.5)
    #pa = Parser.parsePFact("0.5::a.",txt2atom)
    #b = Atom(2)
    #pb = PFact(b, 0.5)
    #pb = Parser.parsePFact("0.5::b.",txt2atom)
    #c = Atom(2)
    #d = Atom(3)
    #e = Atom(4)
    #r1 = Parser.parseRule("c :- a, not d.",txt2atom)
    #r1 = Rule(c, [a], [d])
    #r2 = Parser.parseRule("d :- a, not c.",txt2atom)
    #r2 = Rule(d, [a], [c])
    #r3 = Parser.parseRule("e :- b, not a.",txt2atom)
    #r3 = Rule(e, [b], [a])
    #P = Program([pa, pb], [r1, r2, r3])
    #print(P)
