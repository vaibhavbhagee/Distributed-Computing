SPIN = spin
RUN_FLAGS = -run -v -a -f -DNOREDUCE -DNFAIR=3 -m100000
REPLAY_FLAGS = -t -p
SRC_FILE = elevator-system.pml

replay_trace:
	$(SPIN) $(REPLAY_FLAGS) $(SRC_FILE)

valid_range:
	$(SPIN) $(RUN_FLAGS) -Nvalid_range $(SRC_FILE)

elevator_use_serviced:
	$(SPIN) $(RUN_FLAGS) -Nelevator_use_serviced $(SRC_FILE)

floor_reach_serviced:
	$(SPIN) $(RUN_FLAGS) -Nfloor_reach_serviced $(SRC_FILE)

door_closed_in_motion:
	$(SPIN) $(RUN_FLAGS) -Ndoor_closed_in_motion $(SRC_FILE)

every_floor_infinitely_often:
	$(SPIN) $(RUN_FLAGS) -Nevery_floor_infinitely_often $(SRC_FILE)

clean:
	rm -rf pan* dot* *.trail