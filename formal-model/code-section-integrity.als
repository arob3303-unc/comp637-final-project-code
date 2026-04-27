/* 
 * checksum_integrity.als
 *
 * Models checksum-based CODE_INTEGRITY behavior.
 *
 * Source-level idea:
 * protected section modified
 *   -> periodic checksum integrity check runs
 *   -> checksum violation is recorded
 */

open util/ordering[State] as ord

abstract sig Bool {}
one sig True, False extends Bool {}


sig State {
    // Attacker-caused condition:
    // protected .text/.rdata-style section has been modified.
    protectedSectionModified: one Bool,

    // Whether the periodic checksum check has run.
    checksumCheckRan: one Bool,

    // Internal evidence/violation record.
    checksumViolationRecorded: one Bool,
}

// initial state: clean system, no checks run, no violations, no flags.
pred init[s: State] {
    s.protectedSectionModified = False
    s.checksumCheckRan = False
    s.checksumViolationRecorded = False
}

// 3. TRANSITIONS: Attacker Actions
// Attack Vector 1: Attacker modifies a protected section
pred modifyProtectedSection[s, s_prime: State] {
    s_prime.protectedSectionModified = True

    // Attacker action does not itself run the checksum check.
    s_prime.checksumCheckRan = s.checksumCheckRan

    // No violation is recorded immediately.
    s_prime.checksumViolationRecorded = s.checksumViolationRecorded
}

// Periodic checksum integrity check runs.
pred checkRuns[s, s_prime: State] {
    // The periodic checksum check runs in this step.
    s_prime.checksumCheckRan = True

    // Modification state persists.
    s_prime.protectedSectionModified = s.protectedSectionModified

    // If the protected section is modified, record a checksum violation.
    // This models Integrity::PeriodicIntegrityCheck adding an IntegrityViolation
    // when the recomputed checksum no longer matches the stored baseline.
    (s.protectedSectionModified = True and s_prime.checksumCheckRan = True) =>
        s_prime.checksumViolationRecorded = True
    else
        s_prime.checksumViolationRecorded = s.checksumViolationRecorded
}

/* -------------------------
   Stutter Step
------------------------- */

pred stutter[s, s_prime: State] {
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.checksumCheckRan = s.checksumCheckRan
    s_prime.checksumViolationRecorded = s.checksumViolationRecorded
}

/* -------------------------
   Step Relation
------------------------- */

pred step[s, s_prime: State] {
    modifyProtectedSection[s, s_prime]
    or checkRuns[s, s_prime]
    or stutter[s, s_prime]
}

/* -------------------------
   Trace Definition
------------------------- */

fact Trace {
    init[ord/first]
    all s: State - ord/last | step[s, ord/next[s]] // Every non-final state transistions to the next state by one vaild step
}

/* -------------------------
   Sanity Properties
------------------------- */

// Explicit check that the system starts clean.
assert InitialStateIsClean {
    init[ord/first]
}

// A checksum violation should not appear unless a checksum check has run.
assert NoViolationWithoutChecksumCheck {
    all s: State |
        s.checksumViolationRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.checksumCheckRan = True
}

// A checksum violation should not appear unless the protected section was modified earlier in the trace.
assert NoViolationWithoutModification {
    all s: State |
        s.checksumViolationRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.protectedSectionModified = True
}

assert ModificationMonotonic {
    all s: State - ord/last |
        s.protectedSectionModified = True implies
            ord/next[s].protectedSectionModified = True
}

assert ChecksumViolationMonotonic {
    all s: State - ord/last |
        s.checksumViolationRecorded = True implies
            ord/next[s].checksumViolationRecorded = True
}

/* -------------------------
   Main Security Properties
------------------------- */

// If a protected section is modified and the checksum check runs, a checksum
// violation should be recorded by that transition.
assert ModifiedSectionRecordedWhenCheckRuns {
    all s: State - ord/last |
        (s.protectedSectionModified = True and checkRuns[s, ord/next[s]]) implies
            ord/next[s].checksumViolationRecorded = True
}

/* -------------------------
   Check Commands
------------------------- */

check InitialStateIsClean for 6
check NoViolationWithoutChecksumCheck for 6
check NoViolationWithoutModification for 6
check ModificationMonotonic for 6
check ChecksumViolationMonotonic for 6

check ModifiedSectionRecordedWhenCheckRuns for 6
