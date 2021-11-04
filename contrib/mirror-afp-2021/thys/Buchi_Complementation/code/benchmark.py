#!/usr/bin/python -u

import sys, random, subprocess, time

def read(path):
	with open(path, "r") as f: return f.read()
def write(path, text):
	with open(path, "w") as f: f.write(text)

def measure(action):
	start = time.time()
	result = action()
	return result, time.time() - start

def get_state_count(path):
	result = subprocess.run(["autfilt", path, "--stats=%s"], stdout = subprocess.PIPE, text = True)
	return int(result.stdout.strip())
def get_transition_count(path):
	result = subprocess.run(["autfilt", path, "--stats=%t"], stdout = subprocess.PIPE, text = True)
	return int(result.stdout.strip())

def spot_generate_automaton(state_count, proposition_count):
	seed = random.randrange(0x10000)
	result = subprocess.run(["randaut", "--seed={}".format(seed), "--ba", "--states={}".format(state_count), str(proposition_count)], stdout = subprocess.PIPE, text = True)
	return result.stdout
def spot_generate_formula(proposition_count):
	seed = random.randrange(0x10000)
	result = subprocess.run(["randltl", "--seed={}".format(seed), str(proposition_count)], stdout = subprocess.PIPE, text = True)
	return result.stdout.strip()

def spot_simplify_automaton(path):
	result = subprocess.run(["autfilt", "--ba", "--small", path], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_simplify_automaton(path):
	result = subprocess.run(["owl", "-I", path, "---", "hoa", "---", "optimize-aut", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout

def spot_formula_to_nba(formula):
	result = subprocess.run(["ltl2tgba", "--ba", formula], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_formula_to_nba(formula):
	result = subprocess.run(["owl", "-i", formula, "---", "ltl", "---", "simplify-ltl", "---", "ltl2nba", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_formula_to_nba_opt(formula):
	result = subprocess.run(["owl", "-i", formula, "---", "ltl", "---", "simplify-ltl", "---", "ltl2nba", "---", "optimize-aut", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_formula_to_dra(formula):
	result = subprocess.run(["owl", "-i", formula, "---", "ltl", "---", "simplify-ltl", "---", "ltl2dra", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_formula_to_dra_opt(formula):
	result = subprocess.run(["owl", "-i", formula, "---", "ltl", "---", "simplify-ltl", "---", "ltl2dra", "---", "optimize-aut", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout

def spot_complement(path_input, path_output):
	try: _, time = measure(lambda: write(path_output, subprocess.run(["autfilt", "--complement", "--ba", path_input], timeout = 60, stdout = subprocess.PIPE, text = True).stdout))
	except subprocess.TimeoutExpired: return None
	state_count = get_state_count(path_output)
	transition_count = get_transition_count(path_output)
	return state_count, transition_count, time

def goal_complement(path_input, path_output, tight):
	try: _, time = measure(lambda: subprocess.run(["gc", "complement", "-m", "rank", "-tr" if tight else "-rd", "1", "-o", path_output, path_input], timeout = 60))
	except subprocess.TimeoutExpired:
		subprocess.run(["killall", "java"])
		return None
	state_count = int(subprocess.run(["gc", "stat", "-s", path_output], stdout = subprocess.PIPE, text = True).stdout.strip())
	transition_count = int(subprocess.run(["gc", "stat", "-t", path_output], stdout = subprocess.PIPE, text = True).stdout.strip())
	return state_count, transition_count, time

def bc_complement(path_input, path_output):
	try: _, time = measure(lambda: subprocess.run(["./Autool", "complement_quick", path_input, path_output], timeout = 60))
	except subprocess.TimeoutExpired: return None
	complement = read(path_output).splitlines()
	state_count = int(complement[0].split()[0]) + 1
	transition_count = len(complement)
	return state_count, transition_count, time
def bc_equivalence(path1, path2):
	try: result, time = measure(lambda: subprocess.run(["./Autool", "equivalence", path1, path2], timeout = 60, stdout = subprocess.PIPE, text = True))
	except subprocess.TimeoutExpired: return None
	return result.stdout.strip() == "true", time

def complement(path):
	r1 = spot_complement(path, path + ".spot")
	r2 = goal_complement(path, path + ".goaltr", True)
	r3 = goal_complement(path, path + ".goalrd", False)
	r4 = bc_complement(path, path + ".bc")
	print("{} {} {} {} {}".format(get_state_count(path), r1, r2, r3, r4))
def equivalence(path_1, path_2):
	r = bc_equivalence(path_1, path_2)
	print("{} {} {}".format(get_state_count(path_1), get_state_count(path_2), r))
	if not r: return None
	eq, _ = r
	return eq

if sys.argv[1] == "complement_automaton":
	while True:
		write("a.hoa", spot_generate_automaton(20, 4))
		complement("a.hoa")
if sys.argv[1] == "complement_formula":
	while True:
		while True:
			write("a.hoa", spot_formula_to_nba(spot_generate_formula(4)))
			if get_state_count("a.hoa") == 10: break
		complement("a.hoa")
if sys.argv[1] == "equivalence_random":
	while True:
		write("a.hoa", spot_generate_automaton(100, 4))
		write("b.hoa", spot_generate_automaton(100, 4))
		equivalence("a.hoa", "b.hoa")
if sys.argv[1] == "equivalence_simplify":
	while True:
		write("a.hoa", spot_generate_automaton(20, 4))
		write("b.hoa", spot_simplify_automaton("a.hoa"))
		equivalence("a.hoa", "b.hoa")
if sys.argv[1] == "equivalence_translate":
	while True:
		formula = spot_generate_formula(4)
		write("a.hoa", spot_formula_to_nba(formula))
		write("b.hoa", owl_formula_to_dra_opt(formula))
		write("c.hoa", spot_simplify_automaton("b.hoa"))
		if equivalence("a.hoa", "c.hoa") == False: print(formula)
