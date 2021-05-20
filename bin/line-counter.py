import sys
import re

prog_lines = []
prog_count = 0
prog_total = 0
spec_lines = []
spec_count = 0
spec_total = 0

last_heading = ""

def print_counts(spec_count, prog_count):
    #print last_heading
    print(spec_count, "\t", prog_count, "\t", prog_count + spec_count)
    

def count(fname):
    global prog_total, spec_total, prog_count, spec_count, last_heading
    last_heading = "--- Beginning of " + fname + " ---"
    with open(fname, 'r') as fin:
        spec_context = False
        scope_level = 0
        spec_level = 0
        for line in fin:
            line = line.strip()
            if line == "" or line.startswith("//"):
                continue
            if line.startswith("/** {Spec} "):
                #print_counts(spec_count, prog_count)
                last_heading = line
                if spec_context:
                    spec_total += spec_count + prog_count
                else :
                    prog_total += prog_count
                    spec_total += spec_count
                prog_count, spec_count = 0, 0
                spec_context = True
                scope_level = 1
                continue
            if line.startswith("/**"):
                #print_counts(spec_count, prog_count)
                last_heading = line
                if spec_context:
                    spec_total += spec_count + prog_count
                else :
                    prog_total += prog_count
                    spec_total += spec_count
                prog_count, spec_count = 0, 0
                spec_context = False
                scope_level = 0
                continue

            spec_keywords = [
                "invariant", "requires", "ensures", "auto", "predicate", "function", "==>", "axiom", 
                "define", "split", "&&", "&*&", "||", "pure", "assert", "lemma", "forall", "exists", "ghost",
            ]
            if not spec_context and re.search("assert.*with\s\{", line):
                spec_context = True
                spec_level = scope_level

            scope_level = scope_level + line.count("{") - line.count("}")

            if spec_context or any(w in line for w in spec_keywords):
                #spec_lines.append(line)
                spec_count += 1
            else:
                #prog_lines.append(line)
                prog_count += 1

            if spec_context and scope_level <= spec_level:
                spec_context = False

    spec_total += spec_count
    prog_total += prog_count
    #print_counts(spec_count, prog_count)

    
for file in sys.argv[1:]:
    count(file)

last_heading = "--- End of File(s) ---"
print_counts(spec_total, prog_total)


#if len(sys.argv) > 2 and sys.argv[2] == "debug":
#    print "\nProg lines:"
#    for line in prog_lines:
#        print "  " + line
#
#    print "\n----------\n\nSpec lines:"
#    for line in spec_lines:
#        print "  " + line
