// ===========================================================================
// SWEN90010 2019 - Assignment 2 Submission
// by <Margareta Hardiyanti, 852105>, <Ivan Ken Weng Chee, 736901>
// ===========================================================================

module logger
open util/ordering[State] as ord

// =========================== System State ==================================

// The type of network log messages
sig LogMessage {}

// Meta information in the model that identifies the last action performed
abstract sig Action {}
one sig SendLogMessage, RecvLogMessage extends Action {}

abstract sig AttackerAction extends Action {}
one sig DropMessage, FabricateMessage, ReplayMessage extends AttackerAction {}

// The system state
sig State {
  network    : lone LogMessage, // Network state: holds up to one message
  log        : seq LogMessage,  // The log: a sequence of messages
  last_action: lone Action,     // Identifies the most recent action performed
}

// An axiom that restricts the model to never allow more than one messasge on
// the network at a time; a simplifying assumption to ease the analysis
fact {
  all s : State | lone s.network
}

// =========================== Initial State =================================

// The initial state of the system:
//   - empty network, 
//   - log is empty
pred Init[s : State] {
  no s.network and
  no s.log.elems and
  no s.last_action
}

// =========================== Actions =======================================

// Models the action in which a LogMessage log message is sent
// Precondition : The network is empty
// Postcondition: Network contains a new message
//                last_action is SendLogMessage
//                and nothing else changes
pred send_log_message[s, s' : State] {
  no s.network and
  s'.last_action = SendLogMessage and
  s'.log = s.log and
  some msg : LogMessage | (
    (s'.network = s.network + msg)
  )
}

// Models the action in which a log message is received
// by the logger, causing the log to be updated
// and the message to be removed from the network.
// Precondition : Exists some LogMessage message m on network
// Postcondition: Contents of message m added to the log
//                message m is removed from the network
//                last_action is RecvLogMessage
pred recv_log_message[s, s' : State] {
  some msg : LogMessage | (
    msg in s.network and
    s'.log = s.log.add[msg] and
    s'.network = s.network - msg
  ) and
  s'.last_action = RecvLogMessage
}

// =========================== Attacker Actions ==============================

// This models the action in which the attacker intercepts a
// log message and prevents it from reaching the Logging Service,
// by removing it from the network. 
// Precondition : A message exists on the network
// Postcondition: The message on the network is removed
//                and nothing else changes
pred attacker_action_drop[s, s' : State] {
  some msg : LogMessage | (
    msg in s.network and
    s'.network = s.network - msg
  ) and
  s'.log = s.log and
  s'.last_action = DropMessage
}

// This models the action in which the attacker invents a new
// log message and injects it into the network, to be received
// by the Logging Service. This action can only be performed
// when the network does not already contain a message. 
// Precondition : A message does not exist on the network
// Postcondition: Add a new message on the network
//                and nothing else changes        
pred attacker_action_fabricate[s, s' : State] {
  some msg : LogMessage | (
    no s.network and
    s'.network = s'.network + msg
  ) and
  s'.log = s.log and
  s'.last_action = FabricateMessage
}

// This models the action in which the attacker injects an old
// message onto the network, i.e. a message that was already
// present on the network in some prior state of the model.
// This action can only be performed when the network does
// not already contain a message.
// Precondition : A message does not exist on the network
//			  the message is already present in the log
// Postcondition : Add the message on the network
//                            and nothing else changes   
pred attacker_action_replay[s, s' : State] {
  some s'' : State | (
    s'' in s.prevs and
    some msg : LogMessage | (
      no s.network and
      msg in s''.network and
      s'.network = s.network + msg
    )
  ) and
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
    (all idx : Int | idx < #(s.log) implies s.log[idx] = s'.log[idx])
}

check log_only_grows for 10 expect 0

// Assert the correctness of the log with respect to the execution
// trace leading to state s. If log correct holds for all states s,
// then it should be the case that the log only ever contains
// messages that were sent by the Sender and that the messages
// in the log should not be out of order. 
pred log_correct[s : State] {
  all s' : State | (
	// 
    s' in (prevs[s] + s) and (
      // initial state
      no s'.last_action and
      no s'.log and
      no s'.network
    ) or
	// This method is used to make sure that every time the message is sent by a sender, 
	// it is checked that the message is put on the network
    some msg : LogMessage | (
      s'.last_action in SendLogMessage and
      no prev[s'].last_action and
      msg in s'.network
    ) or (
      // send(A)
	  // This method is used to check that the log stays the same after a send action is executed.
      s'.last_action in SendLogMessage and
      msg in s'.network and
      prev[s'].log.elems in s'.log.elems
    ) or (
      // send(A) > recv(A)
	  // This method is used to make sure that every time the message is received by a receiver, 
	  // the new message stored in the log is the message which has been sent by the sender in the previous state
	  // This also ensures that the message is being sent in correct order without interrupted by something else 
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in SendLogMessage and
      last[s'.log] in prev[s'].network
    ) or (
      // drop(A)
	 // This method indicates that a message could lost in the network, then the message stored in the log should 
	 // not change, means nothing intercepts in between.   
      s'.last_action in DropMessage and
      no s'.network and
      s'.log.elems in prev[s'].log.elems
    ) or (
      // send(A) > drop(A) > recv(A)
	  // This method indicates if a message sent by a sender is dropped by an attacker, then the log message in the receiver state
	  // should be the same with the log message in the state of the message sent. Thus, the log is still considered as correct as it allows
	  // the message lost
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in DropMessage and
      prev[prev[s']].last_action in SendLogMessage and
      msg in prev[prev[s']].network and
      msg not in prev[s'].network and
      s'.log.elems in prev[prev[s']].log.elems
    ) or (
      // send(A) > drop (A) > send(A) 
	  // This method indicates if a message sent by a sender is dropped by an attacker, then a sender tries to send a message, the log message in the
	  // last state should be the same with the log message in the state before the message is dropped.
      s'.last_action in SendLogMessage and
      prev[s'].last_action in DropMessage and
      prev[prev[s']].last_action in SendLogMessage and
      msg in prev[prev[s']].network and
      msg not in prev[s'].network and
      msg in s'.network and
      prev[s'].log.elems in prev[prev[s']].log.elems and
      s'.log.elems in prev[prev[s']].log.elems
    ) or (
      // send(A) > drop (A) > send(A) > recv (A) 
	  // This method indicates if a message sent by a sender is dropped by an attacker, then a sender tries to send a message again and received by the receiver
	  // the log message in the last state should have the message which has been sent by the sender in the previous state, not include the message which has been dropped beforehand
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in SendLogMessage and
      prev[prev[s']].last_action in DropMessage and
      prev[prev[prev[s']]].last_action in SendLogMessage and
      msg not in s'.network and
      msg in prev[s'].network and
      msg not in prev[prev[s']].network and
      msg in prev[s'].network and
      msg in prev[prev[prev[s']]].network and
      (prev[prev[prev[s']]].log.elems + prev[s'].network) in s'.log.elems
    ) or (
      // fabr(A) > recv(A)
	  // This method is used to ensure that if a message received by a receiver is fabricated by an attacker in the previous state, 
	  // the correct log could not have the fabricated message in the log
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in FabricateMessage and
      prev[s'].network not in last[s'.log] and
      s'.log.elems in prev[s'].log.elems
    ) or (
      // repl(A) > recv(A)
 	  // This method used to ensure that if a message received by a receiver is replayed by an attacker in the previous state, 
	  // the correct log could not have the replayed message in the log
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in ReplayMessage and
      prev[s'].network not in last[s'.log] and
      s'.log.elems in prev[s'].log.elems
    ) or (
      // send(A) > lost(A) > repl(A) > recv(A)
	  // This method is to ensure when a sender send a message, then lost in the middle of the state, so the attacker reply the same message
	  // the correct log should not store the message in the log when a receiver receive the message 
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in ReplayMessage and
      prev[prev[s']].last_action in SendLogMessage and
      msg in prev[prev[s']].network and
      msg in prev[s'].network and
      msg not in last[s'.log]
    ) or (
      // send(A) > drop(A) > repl(A) > recv(A)
	  // This method is to ensure when a sender send a message, then lost in the middle of the state, so the attacker reply the same message
	  // the log should not have it stored in the log when a receiver receive the message
      s'.last_action in RecvLogMessage and
      prev[s'].last_action in ReplayMessage and 
      prev[prev[s']].last_action in DropMessage and 
      prev[prev[prev[s']]].last_action in SendLogMessage and 
      msg in prev[prev[prev[s']]].network and	
      msg in prev[prev[s']].network and
      msg in prev[s'].network and
      msg in last[s'.log]
    )
  )
}

// Used to specify the log_correct_* predicates below
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
check log_correct_when_attacker_only_replays for 4 expect 1
/*
  The minimum state to detect the replays attack is 4 states
    State   | Network   | Last Action | Log
    0       | -         | -           | -
    1       | LogMsg0   | SendMsg0    | -
    2       | -         | RecvMsg0    | 0-> LogMsg0
    3       | LogMsg0   | ReplayMsg0  | 0-> LogMsg0
  The attacker replays a message when a message has been sent
  by the sender in the previous state. In the next state, the replayed
  message will be logged in the log, which is incorrect.
 */

assert log_correct_when_attacker_only_fabricates {
  all s : State | attacker_only[FabricateMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_fabricates for 2 expect 1
/*
  The minimum state to detect the fabricate attack is 2 states
    State  | Network   | Last Action   | Log
    0      | -         | -             | -
    1      | LogMsg0   | FabricateMsg0 | -
  The attacker fabricates a new message before anything has been sent.
  In the following state, the log will contain the fabricated message,
  leading to an incorrect log.
 */

// <Describe any additional attacks that are possible but are not
//  captured by your model here>
/*
  Attacks which involve extending the model and log_correct to capture

  1 An attacker could try to edit the message in the network without getting captured by this model, as it 
	will be considered as an original message sent by a sender. In order to capture this behaviour, the model
    needs to contain further signatures for LogMessages to have attributes such as message_content.
    In this way, the attacker can modify the LogMessage contents and send it as if it was sent by
    the Sender but already tampered with.
    
  2 An attacker could store a message somewhere (probably if he/she has their own log), and continue listening
    for further messages sent by the sender. Once another message is sent, the attacker can then send the first
    message to the receiver to cause the messages received to be out of order.

  3 If LogMessages are extended to have unique id attributes, then Alloy will be able to distinguish identical
    messages instead of treating them as the same object. The correct ordering of messages can now distinguish
    if the sender sends the same message twice, or one message has been dropped and subsequently replayed by
    the attacker.

  4 If the system is extended to allow the receiver to send read receipts or acknowlegement back to the sender
    when receiving a message (two way communication), then the sender will be able to identify if his/her
    sent messages are lost by unreliable networks. This may also be a way to detect messages dropped by the attacker

  5 Since this model is based on states of the system, the attacker can only manipulate the network in between
    two states, and has to set their last action as such. For the receiver, a hard constraint may be placed such that
    every action in the state immediately preceeding the current receive state must be a send state. This will render
    the attacker useless unless he/she modifies the last_action of the state. It does sufficiently capture a real
    world scenario where the network is transparent, and both sender and receiver cannot know if a real attacker
    has intercepted the network.

  6 We can add a message lost action to distinguish unreliable networks with the attacker dropping messages. Currently
    there is no method to let Alloy randomly cause messages in the network to disappear.

  Attacks which the existing system captures but possibly not captured by log_correct

  1 If the attacker fabricates a message, then replays that identical message, it may violate the definition of
    replaying sender messages because the attacker has a chance of replaying the message he/she fabricated.

  2 If the attacker does nothing but simply stores messages on the network as they are sent by the sender,
    the attacker is simply equivalent to the receiver, similar to eavesdropping on the network. This may
    possibly be another attacker action, other than the original 3.

 */
