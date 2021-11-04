#!/usr/bin/python

import sys, random, subprocess, time, math

def read(path):
	f = open(path, "r")
	text = f.read()
	f.close
	return text
def write(path, text):
	f = open(path, "w")
	f.write(text)
	f.close()

def stats(entries, finished):
	entry_count = "{}".format(len(entries))
	finished_ratio = "{:.2f} \\%".format(100 * len(finished) / len(entries)) if entries else "N/A"
	finished_time = "{:.3f} s".format(sum(finished) / len(finished)) if finished else "N/A"
	return "{} & {} & {}".format(entry_count, finished_ratio, finished_time)
def stats_entries(entries, label, predicate):
	entries = list(time for (state_count, result, time) in entries if predicate(state_count, result, time))
	finished = list(float(time) for time in entries if time != "T")
	print("{} & {}\\\\".format(label, stats(entries, finished)))

if sys.argv[1] == "states":
	entries = list(line.split() for line in read(sys.argv[2]).splitlines())
	entries = list((int(state_count_1), int(state_count_2), result, time) for [state_count_1, state_count_2, result, time] in entries)
	non_timeout = list(time for (state_count_1, state_count_2, result, time) in entries if time != "T")
	print(all(result == "True" or time == "T" for (state_count_1, state_count_2, result, time) in entries))
	print("completion rate: {}".format(len(non_timeout) / len(entries)))
	print("{} {}".format(sum(state_count_1 for (state_count_1, state_count_2, result, time) in entries) / len(entries), sum(state_count_2 for (state_count_1, state_count_2, result, time) in entries) / len(entries)))

if sys.argv[1] == "complement":
	entries = list(line.split() for line in read(sys.argv[2]).splitlines())
	entries = list(time for [state_count, time] in entries)
	non_timeout = list(float(time) for time in entries if time != "T")
	print(stats(entries, non_timeout))
if sys.argv[1] == "equivalence":
	segments = 4
	size = 5
	entries = list(line.split() for line in read(sys.argv[2]).splitlines())
	entries = list((max(int(state_count_1), int(state_count_2)), result, time) for [state_count_1, state_count_2, result, time] in entries)
	print(all(result == "True" or time == "T" for (state_count, result, time) in entries))
	for n in range(segments): stats_entries(entries, "$({}, {}]$".format(n * size, (n + 1) * size), lambda state_count, result, time: n * size < state_count and state_count <= (n + 1) * size)
	stats_entries(entries, "$({}, \infty)$".format(segments * size), lambda state_count, result, time: segments * size < state_count)
	print("\hline")
	stats_entries(entries, "total", lambda state_count, result, time: True)
if sys.argv[1] == "compare":
	def read_block(blocks):
		if blocks[0] == 'None': return (None, blocks[1:])
		return (int(blocks[0]), int(blocks[1]), float(blocks[2])), blocks[3:]
	def parse(line):
		blocks = line.replace(',', '').replace('(', '').replace(')', '').split()
		state_count, blocks = int(blocks[0]), blocks[1:]
		r1, blocks = read_block(blocks)
		r2, blocks = read_block(blocks)
		r3, blocks = read_block(blocks)
		r4, blocks = read_block(blocks)
		return r1, r2, r3, r4
	def stats(label, entries, finished, completed):
		def round_(digits, value): return float(('%.' + str(digits) + 'g') % value)
		def digits(digits, value): return round(value, digits -int(math.floor(math.log10(abs(value)))) - 1)
		ratio = "{:.2f} \\%".format(100 * len(finished) / len(entries))
		time = "{:.3f} s".format(sum(time for _, _, time in completed) / len(completed))
		states = "{:g}".format(digits(4, sum(states for states, _, _ in completed) / len(completed)))
		return "{} & {} & {} & {}\\\\".format(label, ratio, time, states)
	entries = list(parse(line) for line in read(sys.argv[2]).splitlines())
	completed = list(entry for entry in entries if all(entry))
	print("finished by all: {} of {}".format(len(completed), len(entries)))
	label = ["Spot (\\texttt{-{}-complement -{}-ba})", "\\textsc{Goal} (\\texttt{rank -tr})", "\\textsc{Goal} (\\texttt{rank -rd})", "Our Tool"]
	for index in range(4):
		block_entries = list(entry[index] for entry in entries)
		block_finished = list(entry[index] for entry in entries if entry[index] is not None)
		block_completed = list(entry[index] for entry in completed)
		print(stats(label[index], block_entries, block_finished, block_completed))
