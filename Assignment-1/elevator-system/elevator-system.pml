bit lift_switch[3] // Switches present in the elevator
bit floor_switch[3] // Switches present on the floors

bit door_state // 1 for open and 0 for closed

byte curr_floor // current floor of the elevator - Should take values 0, 1, 2

// Type of messages to be passed among the processes
mtype = {open_door, close_door, move_up, move_down, stop, press_floor_button, press_elevator_button}

// Channel definitions
chan to_elevator = [0] of { mtype } // Channel to send instructions from controller to elevator
chan button_press = [0] of { mtype, byte} // Channel to record button presses

// Models the elevator controller
proctype elevator_controller()
{

}

// Models the elevator
proctype elevator()
{

}

// Models the elevator and floor button presses
proctype press_buttons()
{

}

// Records the button presses for the controller
proctype record_button_presses()
{

}