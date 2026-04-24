/*
 * debugger-model.als
 *
 * This model captures the debugger detection pipeline:
 *
 *   Debugger attaches to process
 *        -> periodic monitor/debugger detection check runs
 *        -> DEBUGGER_DETECTED flag is recorded
 *
 * In the source code, the monitor checks whether a debugger is attached
 * to the process (via IsDebuggerPresent, CheckRemoteDebuggerPresent, PEB flags, etc).
 * If so, it records DetectionFlags::DEBUGGER_DETECTED through EvidenceManager->AddFlagged(...).
 */

open util/ordering[State] as ord

abstract sig Bool {}
one sig True, False extends Bool {}

sig State {
    // Attacker-caused condition:
    // A debugger is attached to the running process.
    debuggerAttached: one Bool,

    // Whether the periodic debugger detection check has run.
    debuggerCheckRan: one Bool,

    // Internal evidence/violation record.
    debuggerDetectionRecorded: one Bool
}

// Initial state: clean system, no debugger attached, no checks run, no violations.
pred init[s: State] {
    s.debuggerAttached = False
    s.debuggerCheckRan = False
    s.debuggerDetectionRecorded = False
}

/* -------------------------
   Attacker Action
------------------------- */

// Attack Vector: Attacker attaches a debugger to the process
pred attachDebugger[s, s_prime: State] {
    // Debugger is now attached
    s_prime.debuggerAttached = True

    // Attacker action does not itself run the debugger detection check
    s_prime.debuggerCheckRan = s.debuggerCheckRan

    // No detection is recorded immediately
    s_prime.debuggerDetectionRecorded = s.debuggerDetectionRecorded
}

/* -------------------------
   Debugger Detection Check
------------------------- */

// Periodic debugger detection check runs
pred runDebuggerDetectionCheck[s, s_prime: State] {
    // The periodic debugger detection check runs in this step
    s_prime.debuggerCheckRan = True

    // The attacker-caused debugger attachment persists
    s_prime.debuggerAttached = s.debuggerAttached

    // If a debugger is attached, record a debugger detection
    // Otherwise, preserve the previous detection state
    s.debuggerAttached = True =>
        s_prime.debuggerDetectionRecorded = True
    else
        s_prime.debuggerDetectionRecorded = s.debuggerDetectionRecorded
}

/* -------------------------
   Stutter Step
------------------------- */

pred stutter[s, s_prime: State] {
    // No action occurs in this step
    s_prime.debuggerAttached = s.debuggerAttached
    s_prime.debuggerCheckRan = s.debuggerCheckRan
    s_prime.debuggerDetectionRecorded = s.debuggerDetectionRecorded
}

/* -------------------------
   Step Relation
------------------------- */

pred step[s, s_prime: State] {
    attachDebugger[s, s_prime]
    or runDebuggerDetectionCheck[s, s_prime]
    or stutter[s, s_prime]
}

/* -------------------------
   Trace Definition
------------------------- */

fact Trace {
    init[ord/first]

    // Every non-final state transitions to the next state by one valid step
    all s: State - ord/last | step[s, ord/next[s]]
}

/* -------------------------
   Sanity Properties
------------------------- */

/*
 * Explicit check that the system starts clean.
 */
assert InitialStateIsClean {
    init[ord/first]
}

/*
 * A DEBUGGER_DETECTED flag should not appear unless a debugger detection
 * check has run earlier in the trace.
 */
assert NoDetectionWithoutDebuggerCheck {
    all s: State |
        s.debuggerDetectionRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.debuggerCheckRan = True
}

/*
 * A DEBUGGER_DETECTED flag should not appear unless a debugger
 * was attached earlier in the trace.
 */
assert NoDetectionWithoutDebuggerAttachment {
    all s: State |
        s.debuggerDetectionRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.debuggerAttached = True
}

/*
 * Once a debugger has been attached, that condition persists in this abstraction.
 */
assert DebuggerAttachmentMonotonic {
    all s: State - ord/last |
        s.debuggerAttached = True implies
            ord/next[s].debuggerAttached = True
}

/*
 * Once a DEBUGGER_DETECTED flag has been recorded, it persists.
 * This matches the abstraction of a DetectionFlags::DEBUGGER_DETECTED
 * entry being stored in the evidence/flag list.
 */
assert DebuggerDetectionMonotonic {
    all s: State - ord/last |
        s.debuggerDetectionRecorded = True implies
            ord/next[s].debuggerDetectionRecorded = True
}

/* -------------------------
   Main Security Property
------------------------- */

/*
 * If a debugger is attached to the process, then a DEBUGGER_DETECTED flag
 * should eventually be recorded.
 */
assert DebuggerAttachmentEventuallyDetected {
    all s: State |
        s.debuggerAttached = True implies
            some t: s.*(ord/next) |
                t.debuggerDetectionRecorded = True
}

/* -------------------------
   Check Commands
------------------------- */

check InitialStateIsClean for 6
check NoDetectionWithoutDebuggerCheck for 6
check NoDetectionWithoutDebuggerAttachment for 6
check DebuggerAttachmentMonotonic for 6
check DebuggerDetectionMonotonic for 6

check DebuggerAttachmentEventuallyDetected for 6

