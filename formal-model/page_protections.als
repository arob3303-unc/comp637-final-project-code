/*
 * page_protections.als
 *
 *   protected section made writable
 *        -> periodic monitor/page-protection check runs
 *        -> PAGE_PROTECTIONS flag is recorded
 */

 open util/ordering[State] as ord

abstract sig Bool {}
one sig True, False extends Bool {}

sig State {
    protectedSectionWritable: one Bool,
    pageProtectionCheckRan: one Bool,
    pageProtectionFlagRecorded: one Bool
}

pred init[s: State] {
    s.protectedSectionWritable = False
    s.pageProtectionCheckRan = False
    s.pageProtectionFlagRecorded = False
}

/* -------------------------
   Attacker Action
------------------------- */

pred makeProtectedSectionWritable[s, s_prime: State] {
    s_prime.protectedSectionWritable = True
    s_prime.pageProtectionCheckRan = s.pageProtectionCheckRan
    s_prime.pageProtectionFlagRecorded = s.pageProtectionFlagRecorded
}

/* -------------------------
   Page Protection Check
------------------------- */

pred runPageProtectionCheck[s, s_prime: State] {
    s_prime.pageProtectionCheckRan = True
    s_prime.protectedSectionWritable = s.protectedSectionWritable

    s.protectedSectionWritable = True =>
        s_prime.pageProtectionFlagRecorded = True
    else
        s_prime.pageProtectionFlagRecorded = s.pageProtectionFlagRecorded
}

/* -------------------------
   Stutter Step
------------------------- */

pred stutter[s, s_prime: State] {

    // No action occurs in this step.

    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.pageProtectionCheckRan = s.pageProtectionCheckRan
    s_prime.pageProtectionFlagRecorded = s.pageProtectionFlagRecorded
}

/* -------------------------
   Step Relation
------------------------- */

pred step[s, s_prime: State] {
    makeProtectedSectionWritable[s, s_prime]
    or runPageProtectionCheck[s, s_prime]
    or stutter[s, s_prime]
}

/* -------------------------
   Trace Definition
------------------------- */

fact Trace {
    init[ord/first]

    all s: State - ord/last | step[s, ord/next[s]] // Every non-final state transitions to the next state by one valid step.
}

/* -------------------------
   Sanity Properties
------------------------- */

/*
 * The trace begins in a clean state.
 */
assert InitialStateIsClean {
    init[ord/first]
}

/*
 * A PAGE_PROTECTIONS flag should not appear unless a page-protection
 * check has run earlier in the trace.
 */
assert NoFlagWithoutPageProtectionCheck {
    all s: State |
        s.pageProtectionFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.pageProtectionCheckRan = True
}

/*
 * A PAGE_PROTECTIONS flag should not appear unless the protected section
 * was writable earlier in the trace.
 */
assert NoFlagWithoutWritableSection {
    all s: State |
        s.pageProtectionFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.protectedSectionWritable = True
}

/*
 * Once a protected section has been made writable, that condition persists
 * in this abstraction.
 */
assert WritableSectionMonotonic {
    all s: State - ord/last |
        s.protectedSectionWritable = True implies
            ord/next[s].protectedSectionWritable = True
}

/*
 * Once a PAGE_PROTECTIONS flag has been recorded, it persists.
 * This matches the abstraction of a DetectionFlags::PAGE_PROTECTIONS
 * entry being stored in the evidence/flag list.
 */
assert PageProtectionFlagMonotonic {
    all s: State - ord/last |
        s.pageProtectionFlagRecorded = True implies
            ord/next[s].pageProtectionFlagRecorded = True
}

/* -------------------------
   Main Security Property
------------------------- */

/*
 * If a protected section is made writable, then a PAGE_PROTECTIONS flag
 * should eventually be recorded.
 *
 */
assert WritableSectionEventuallyFlagged {
    all s: State |
        s.protectedSectionWritable = True implies
            some t: s.*(ord/next) |
                t.pageProtectionFlagRecorded = True
}

/* -------------------------
   Check Commands
------------------------- */

check InitialStateIsClean for 6
check NoFlagWithoutPageProtectionCheck for 6
check NoFlagWithoutWritableSection for 6
check WritableSectionMonotonic for 6
check PageProtectionFlagMonotonic for 6

check WritableSectionEventuallyFlagged for 6
