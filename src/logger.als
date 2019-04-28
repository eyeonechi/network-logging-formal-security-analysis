// ===========================================================================
// SWEN90010 2019 - Assignment 2 Submission
// by <Margareta Hardiyanti, 852105>, <Ivan Ken Weng Chee, 736901>
// ===========================================================================

module logger
open util/ordering[State] as ord

// =========================== System State ==================================

// the type of network log messages
sig LogMessage {}

// meta information in the model that identifies the last action performed
abstract sig Action {}
one sig SendLogMessage, RecvLogMessage 
        extends Action {}

abstract sig AttackerAction extends Action {}
one sig DropMessage, FabricateMessage, ReplayMessage extends AttackerAction {}

// The system state
sig State {
  network : lone LogMessage,       // Network state: holds up to one message
  log     : seq LogMessage,        // The log: a sequence of messages
  last_action : lone Action,       // identifies the most recent action 
                                   // performed
}

// an axiom that restricts the model to never allow more than one messasge on
// the network at a time; a simplifying assumption to ease the analysis
fact {
  all s : State | lone s.network
}

// =========================== Initial State =================================

// The initial state of the system:
//   - empty network, 
//   - log is empty
pred Init[s : State] {
  no s.network and no s.log.elems and
  no s.last_action
}

// =========================== Actions =======================================

// Models the action in which a LogMessage log message is sent
// Precondition: the network is empty
// Postcondition: network contains a new message
//                last_action is SendLogMessage
//                and nothing else changes
pred send_log_message[s, s' : State] {
  no s.network and
  s'.last_action = SendLogMessage and
  s'.log = s.log and
  (some msg : LogMessage | 
    (s'.network = s.network + msg))
}

// Models the action in which a log message is received
// by the logger, causing the log to be updated
// and the message to be removed from the network.
// Precondition: exists some LogMessage message m on network
// Postcondition: contents of message m added to the log
//                message m is removed from the network
//                last_action is RecvLogMessage
pred recv_log_message[s, s' : State] {
  (some msg : LogMessage | 
       msg in s.network and s'.log = s.log.add[msg] and
       s'.network = s.network - msg) and
  s'.last_action = RecvLogMessage
}

// =========================== Attacker Actions ==============================

// This models the action in which the attacker intercepts a
// log message and prevents it from reaching the Logging Service,
// by removing it from the network. 
pred attacker_action_drop[s, s' : State] {
  (some msg : LogMessage |
    msg in s.network and
    s'.network = s.network - msg) and
  s'.log = s.log and
  s'.last_action = DropMessage
}

// This models the action in which the attacker invents a new
// log message and injects it into the network, to be received
// by the Logging Service. This action can only be performed
// when the network does not already contain a message. 
pred attacker_action_fabricate[s, s' : State] {
  (some msg : LogMessage |
    no s.network and
    msg not in s.log.elems and
    s'.network = s'.network + msg) and
  s'.log = s.log and
  s'.last_action = FabricateMessage
}

// This models the action in which the attacker injects an old
// message onto the network, i.e. a message that was already
// present on the network in some prior state of the model.
// This action can only be performed when the network does
// not already contain a message.
pred attacker_action_replay[s, s' : State] {
  (some s'' : State |
    s'' in s.prevs and
    (some msg : LogMessage |
      no s.network and
      msg in s''.network and
      s'.network = s.network + msg)) and
  s'.log = s.log and
  s'.last_action = ReplayMessage
}

// =========================== State Transitions and Traces ==================

// State transitions occur via the various actions of the system above
// including those of the attacker.
pred state_transition[s, s' : State] {
  send_log_message[s,s']
  or recv_log_message[s,s']
  or attacker_action_drop[s,s']
  or attacker_action_fabricate[s,s']
  or attacker_action_replay[s,s']
}

// Define the linear ordering on states to be that generated by the
// state transitions above, defining execution traces to be sequences
// of states in which each state follows in the sequence from the last
// by a state transition.
fact state_transition_ord {
  all s: State, s': ord/next[s] {
    state_transition[s,s'] and s' != s
  }
}

// The initial state is first in the order, i.e. all execution traces
// that we model begin in the initial state described by the Init predicate
fact init_state {
  all s: ord/first {
    Init[s]
  }
}

// =========================== Properties ====================================

// An example assertion and check:
// Specifies that the log only grows, i.e. new things can get
// added to it but nothing is ever removed
assert log_only_grows {
  all s : State | all s' : ord/nexts[s] |
     some (s.log.elems) implies 
     (all idx : Int | idx < #(s.log) implies  s.log[idx] = s'.log[idx])
}

check log_only_grows for 10 expect 0

// Assert the correctness of the log with respect to the execution
// trace leading to state s. If log correct holds for all states s,
// then it should be the case that the log only ever contains
// messages that were sent by the Sender and that the messages
// in the log should not be out of order. 
pred log_correct[s : State] {
  (all s' : State |
    s' in (prevs[s] + s) and
    ( // initial state
        no s'.last_action and no s'.log and no s'.network
    ) or
    (some msg : LogMessage |
      (
	 s'.last_action in SendLogMessage and
        no prev[s'].last_action and
        msg in s'.network
        //prev[s'].log.elems in s'.log.elems
      ) or (
        s'.last_action in SendLogMessage and
        msg in s'.network and
        prev[s'].log.elems in s'.log.elems
      ) or (
        // send(A) > recv(A)
        s'.last_action in RecvLogMessage and
        prev[s'].last_action in SendLogMessage and
        last[s'.log] in prev[s'].network
	// s'.log.elems in (prev[s'].log.elems + msg) and
        
   //	msg not in s'.network
   	  ) or (
          s'.last_action in DropMessage and
          no s'.network and
          s'.log.elems in prev[s'].log.elems
         ) or (
        //send(A) > recv(A) > send(A) > drop(A) > recv(A)
      	 s'.last_action in RecvLogMessage and
        prev[s'].last_action in DropMessage and
        prev[prev[s']].last_action in SendLogMessage and
        msg in prev[prev[s']].network and
        msg not in prev[s'].network and
        s'.log.elems in prev[prev[s']].log.elems
	) or (
 	//send(A) > drop (A) > send(A) 
	 s'.last_action in SendLogMessage and
        prev[s'].last_action in DropMessage and
        prev[prev[s']].last_action in SendLogMessage and
   	 msg in prev[prev[s']].network and
        msg not in prev[s'].network and
	 msg in s'.network and
	 prev[s'].log.elems in prev[prev[s']].log.elems and
        s'.log.elems in prev[prev[s']].log.elems
	) or (
	//send(A) > drop (A) > send(A) > recv (A) 
	 s'.last_action in RecvLogMessage and
        prev[s'].last_action in SendLogMessage and
        prev[prev[s']].last_action in DropMessage and
	 prev[prev[prev[s']]].last_action in SendLogMessage and
	 msg not in s'.network and
 	 msg in prev[s'].network and
   	 msg not in prev[prev[s']].network and
        msg in prev[s'].network and
	 msg in prev[prev[prev[s']]].network and
	 (prev[prev[prev[s']]].log.elems + prev[s'].network) in s'.log.elems// and
      //  s'.log.elems in prev[prev[s']].log.elems
       ) or (
         s'.last_action in RecvLogMessage and
         prev[s'].last_action in FabricateMessage and
         prev[s'].network not in last[s'.log] and
         s'.log.elems in prev[s'].log.elems
       ) or (
         s'.last_action in RecvLogMessage and
         prev[s'].last_action in ReplayMessage and
         prev[s'].network not in last[s'.log] and
         s'.log.elems in prev[s'].log.elems
  /*    ) or (
        // fabr(A) > recv(A)
        s'.last_action in RecvLogMessage and
        prev[s'].last_action in FabricateMessage and
        msg in prev[s'].network and
        msg not in last[s'.log]
      ) or (
        // send(A) > lost(A) > repl(A) > recv(A)
        s'.last_action in RecvLogMessage and
        prev[s'].last_action in ReplayMessage and
        prev[prev[s']].last_action in SendLogMessage and
        msg in prev[prev[s']].network and
        msg in prev[s'].network and
        msg not in last[s'.log]
      ) or (
         // send(A) > drop(A) > repl(A) > recv(A)
        s'.last_action in RecvLogMessage and
        prev[s'].last_action in ReplayMessage and 
        prev[prev[s']].last_action in DropMessage and 
        prev[prev[prev[s']]].last_action in SendLogMessage and 
        msg in prev[prev[prev[s']]].network and	
        msg in prev[prev[s']].network and
        msg in prev[s'].network and
        msg in last[s'.log]*/
      )
    )
  )
}

// used to specify the log_correct_* predicates below
pred attacker_only[actions : AttackerAction] {
  all s : State | s.last_action in AttackerAction implies s.last_action in actions
}

assert log_correct_when_attacker_only_drops {
  all s : State | attacker_only[DropMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_drops for 10 expect 0

assert log_correct_when_attacker_only_replays {
  all s : State | attacker_only[ReplayMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_replays for 10 expect 1
// <Add attack description here>

assert log_correct_when_attacker_only_fabricates {
  all s : State | attacker_only[FabricateMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_fabricates for 10 expect 1
// <Add attack description here>

// <Describe any additional attacks that are possible but are not
//  captured by your model here>
