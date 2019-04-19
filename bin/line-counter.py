import sys
import re

prog_lines = []
prog_count = 0
spec_lines = []
spec_count = 0

last_heading = "--- Beginning of file ---"

def print_counts():
    print last_heading
    print "Prog: ", prog_count, " Spec: ", spec_count, " Total: ", prog_count + spec_count
    

fname = sys.argv[1]
with open(fname, 'r') as fin:
    spec_context = False
    scope_level = 0
    spec_level = 0
    for line in fin:
        line = line.strip()
        if line == "" or line.startswith("//"):
            continue
        if line.startswith("/**"):
            print_counts()
            last_heading = line
            prog_count, spec_count = 0, 0
            continue
        
        spec_keywords = [
            "invariant", "requires", "ensures", "predicate", "function", "==>", "axiom", 
            "define", "split", "&&", "&*&", "||", "pure", "assert", "lemma", "forall", "exists", "ghost",
        ]
        if not spec_context and re.search("assert.*with\s\{", line):
            spec_context = True
            spec_level = scope_level
            
        scope_level = scope_level + line.count("{") - line.count("}")

        if spec_context or any(w in line for w in spec_keywords):
            spec_lines.append(line)
            spec_count += 1
        else:
            prog_lines.append(line)
            prog_count += 1

        if spec_context and scope_level <= spec_level:
            spec_context = False
        
print_counts()

if len(sys.argv) > 2 and sys.argv[2] == "debug":
    print "\nProg lines:"
    for line in prog_lines:
        print "  " + line

    print "\n----------\n\nSpec lines:"
    for line in spec_lines:
        print "  " + line
