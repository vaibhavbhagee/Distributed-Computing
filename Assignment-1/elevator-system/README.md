# Description
* Modeling of an elevator system and verification of safety and fairness properties, over the model. 
* There are five process types in this system:
    - Elevator controller
    - Elevator
    - Floor Buttons
    - Elevator Buttons
    - Process to record button presses
* The elevator controller uses the [Elevator Algorithm](https://en.wikipedia.org/wiki/Elevator_algorithm).
* The Elevator controller communicates its instructions to the Elevator, over a channel of size 0, to ensure handshaking of the two processes.
* The Floor Buttons and the Elevator Buttons also communicate the button presses to the process recording the button presses, over a channel of size 0, to ensure handshaking.
* The model assumes that every floor has only one button, to call the elevator to that floor. Whether to go Up or Down is decided once the elevator doors open, on the floor.
* When no requests are to be serviced, the elevator stays idle, with its doors open.

# Installing Spin
* Install Spin, on a Linux machine, as instructed [here](http://spinroot.com/spin/Man/1_Exercises.html).

# Spin and Promela Basics
* The program has been written in Promela (Process Meta Language).
* For Promela basics, visit the [Basic Spin Manual](http://spinroot.com/spin/Man/Manual.html).
* For some examples on Spin Verification, take a look at the [Spin Verification Examples](spinroot.com/spin/Man/1_Exercises.html).
* The code for all the processes resides in the [elevator-system.pml](./elevator-system.pml) file.

# Running the Code
* Spin is an [explicit state model checker](https://en.wikipedia.org/wiki/Model_checking#Explicit-state_model_checking). 
* As a result, for every property, expressed in [Linear Temporal Logic](https://en.wikipedia.org/wiki/Linear_temporal_logic), it creates and runs an executable to perform an exhaustive state space search to verify the property.
* In case of a property violation, it prints a trace file with the set of transitions, leading to the violations.
* The properties considered, and the way to generate and run the executable for each of those is as follows:
    - The elevator, never moves with its doors open.
        + `make door_closed_in_motion`
    - The elevator visits every floor infinitely often.
        + `make every_floor_infinitely_often`
    - Requests to use the elevator are eventually serviced.
        + `make elevator_use_serviced`
    - Requests to be delivered to a particular floor are eventually serviced.
        + `make floor_reach_serviced`
* In case of a property violation, a *.trail* file is generated. To replay the latter, do the following:
    - `make replay_trace`

# Important links
* The [Spin](http://spinroot.com/spin/whatispin.html) model checker.
* A discussion on proving fairness properties using [progress states](https://www.cse.msu.edu/~cse470/PromelaManual/progress.html).
* [LTL formulae](http://spinroot.com/spin/Man/ltl.html) for specifying safety and liveness properties in Spin.
* Enabling [weak fairness](https://spinroot.com/fluxbb/viewtopic.php?id=671) in Spin.
