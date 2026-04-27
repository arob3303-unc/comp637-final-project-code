/*
 * tls_integrity.als
 *
 * This model captures the TLS integrity pipeline:
 *
 *   TLS callback structure is modified
 *        -> periodic monitor/TLS integrity check runs
 *        -> CODE_INTEGRITY flag is recorded
 *
 * In the source code, the monitor checks whether the TLS callback
 * structure has been modified. If so, it records
 * DetectionFlags::CODE_INTEGRITY through EvidenceManager->AddFlagged(...).
 */

open util/ordering[State] as ord

abstract sig Bool {}
one sig True, False extends Bool {}

sig State {
    tlsCallbackModified: one Bool,
    tlsIntegrityCheckRan: one Bool,
    codeIntegrityFlagRecorded: one Bool
}

pred init[s: State] {
    s.tlsCallbackModified = False
    s.tlsIntegrityCheckRan = False
    s.codeIntegrityFlagRecorded = False
}

/* -------------------------
   Attacker Action
------------------------- */

pred modifyTLSCallbackStructure[s, s_prime: State] {
    s_prime.tlsCallbackModified = True
    s_prime.tlsIntegrityCheckRan = s.tlsIntegrityCheckRan
    s_prime.codeIntegrityFlagRecorded = s.codeIntegrityFlagRecorded
}

/* -------------------------
   TLS Integrity Check
------------------------- */

pred checkRuns[s, s_prime: State] {
    s_prime.tlsIntegrityCheckRan = True

    /*
     * The attacker-caused TLS modification persists.
     */
    s_prime.tlsCallbackModified = s.tlsCallbackModified

    /*
     * If the TLS callback structure is modified, record a CODE_INTEGRITY flag.
     * Otherwise, preserve the previous flag state.
     */
    (s.tlsCallbackModified = True and s_prime.tlsIntegrityCheckRan = True) =>
        s_prime.codeIntegrityFlagRecorded = True
    else
        s_prime.codeIntegrityFlagRecorded = s.codeIntegrityFlagRecorded
}

/* -------------------------
   Stutter Step
------------------------- */

pred stutter[s, s_prime: State] {
    /*
     * No action occurs in this step.
     */
    s_prime.tlsCallbackModified = s.tlsCallbackModified
    s_prime.tlsIntegrityCheckRan = s.tlsIntegrityCheckRan
    s_prime.codeIntegrityFlagRecorded = s.codeIntegrityFlagRecorded
}

/* -------------------------
   Step Relation
------------------------- */

pred step[s, s_prime: State] {
    modifyTLSCallbackStructure[s, s_prime]
    or checkRuns[s, s_prime]
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
 * Explicit Check that the trace begins in a clean state.
 */
assert InitialStateIsClean {
    init[ord/first]
}

/*
 * A CODE_INTEGRITY flag should not appear unless the TLS integrity
 * check has run earlier in the trace.
 */
assert NoFlagWithoutTLSIntegrityCheck {
    all s: State |
        s.codeIntegrityFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.tlsIntegrityCheckRan = True
}

/*
 * A CODE_INTEGRITY flag should not appear unless the TLS callback
 * structure was modified earlier in the trace.
 */
assert NoFlagWithoutTLSModification {
    all s: State |
        s.codeIntegrityFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.tlsCallbackModified = True
}

/*
 * Once the TLS callback structure has been modified, that condition
 * persists in this abstraction.
 */
assert TLSModificationMonotonic {
    all s: State - ord/last |
        s.tlsCallbackModified = True implies
            ord/next[s].tlsCallbackModified = True
}

/*
 * Once a CODE_INTEGRITY flag has been recorded, it persists.
 * This matches the abstraction of a DetectionFlags::CODE_INTEGRITY
 * entry being stored in the evidence/flag list.
 */
assert CodeIntegrityFlagMonotonic {
    all s: State - ord/last |
        s.codeIntegrityFlagRecorded = True implies
            ord/next[s].codeIntegrityFlagRecorded = True
}

/* -------------------------
   Main Security Property
------------------------- */

/*
 * If the TLS callback structure is modified and the TLS integrity check runs,
 * then a CODE_INTEGRITY flag should be recorded by that transition.
 */
assert TLSModificationFlaggedWhenCheckRuns {
    all s: State - ord/last |
        (s.tlsCallbackModified = True and checkRuns[s, ord/next[s]]) implies
            ord/next[s].codeIntegrityFlagRecorded = True
}

/* -------------------------
   Check Commands
------------------------- */

check InitialStateIsClean for 6
check NoFlagWithoutTLSIntegrityCheck for 6
check NoFlagWithoutTLSModification for 6
check TLSModificationMonotonic for 6
check CodeIntegrityFlagMonotonic for 6

check TLSModificationFlaggedWhenCheckRuns for 6
