SPIN = spin
FLAGS = -run -v -a -f -DNOREDUCE -DNFAIR=3 -m100000
SRC_FILE = elevator-system.pml

valid_range:
	$(SPIN) $(FLAGS) -Nvalid_range $(SRC_FILE)

elevator_use_serviced:
	$(SPIN) $(FLAGS) -Nelevator_use_serviced $(SRC_FILE)

door_closed_in_motion:
	$(SPIN) $(FLAGS) -Ndoor_closed_in_motion $(SRC_FILE)

clean:
	rm -rf pan* dot* *.trail