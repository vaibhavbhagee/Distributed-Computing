SPIN = spin
MAX_DEPTH = 100000
RUN_FLAGS = -run -v -DNOREDUCE -DNFAIR=3 -m$(MAX_DEPTH)
SAFETY_FLAGS = -a -f
FAIRNESS_FLAGS = -l -f
REPLAY_FLAGS = -t -p
SRC_FILE = elevator-system.pml

replay_trace:
	$(SPIN) $(REPLAY_FLAGS) $(SRC_FILE)

valid_range:
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -Nvalid_range $(SRC_FILE)

elevator_use_serviced:
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -Nelevator_use_serviced $(SRC_FILE)

floor_reach_serviced:
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -Nfloor_reach_serviced $(SRC_FILE)

door_closed_in_motion:
	$(SPIN) $(RUN_FLAGS) $(SAFETY_FLAGS) -Ndoor_closed_in_motion $(SRC_FILE)

every_floor_infinitely_often:
	$(SPIN) $(RUN_FLAGS) $(FAIRNESS_FLAGS) $(SRC_FILE)

clean:
	rm -rf pan* dot* *.trail *.tmp