import sys

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
            "invariant", "requires", "ensures", "predicate", "function", "==>",
            "define", "split", "&&", "&*&", "||", "lemma", "forall", "exists", "ghost",
        ]
        if any(w in line for w in spec_keywords):
            spec_lines.append(line)
            spec_count += 1
        else:
            prog_lines.append(line)
            prog_count += 1
print_counts()

if len(sys.argv) > 2 and sys.argv[2] == "debug":
    print "\nProg lines:"
    for line in prog_lines:
        print "  " + line

    print "\n----------\n\nSpec lines:"
    for line in spec_lines:
        print "  " + line
