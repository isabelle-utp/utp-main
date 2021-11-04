all: PDDL_Checker

PDDL_Checker: PDDL_Checker.mlb PDDL_Checker.sml PDDL_Checker_Exported.sml Unsynchronized.sml
	mlton -verbose 1 -default-type intinf -output PDDL_Checker PDDL_Checker.mlb

PDDL_Checker_prof: PDDL_Checker.mlb PDDL_Checker.sml PDDL_Checker_Exported.sml Unsynchronized.sml
	mlton -verbose 1 -default-type intinf -profile time -output PDDL_Checker_prof PDDL_Checker.mlb
#	mlton -verbose 1 -default-type intinf -profile time -const 'Exn.keepHistory true' -output PDDL_Checker_prof PDDL_Checker.mlb
	
install: PDDL_Checker
	cp PDDL_Checker "$(HOME)/bin/"
