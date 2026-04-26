/*
 * manual_mapping.als
 *
 * This model captures the manual mapped module detection pipeline:
 *
 *   suspicious executable region exists outside known loaded modules
 *        -> periodic monitor/manual-mapping check runs
 *        -> MANUAL_MAPPING flag is recorded
 *
 * In the source code, DetectManualMapping scans committed executable memory
 * regions. It skips regions that are part of known modules. A remaining region
 * is treated as suspicious if it either still has a PE header, or if the PE
 * header appears erased but the region is private and contains possible section
 * bytes. The monitor records DetectionFlags::MANUAL_MAPPING when one or more
 * suspicious regions are returned.
 */

open util/ordering[State] as ord

abstract sig Bool {}
one sig True, False extends Bool {}

sig State {
    // Attacker-caused condition:
    // A manually mapped region exists in the process.
    manualMappedRegionPresent: one Bool,

    // Source-level scan gates from DetectManualMapping.
    regionCommitted: one Bool,
    regionExecutable: one Bool,
    regionInKnownModule: one Bool,

    // Source-level suspicious-region branches.
    peHeaderPresent: one Bool,
    erasedHeaderHeuristicMatched: one Bool,

    // Whether the periodic manual-mapping detection check has run.
    manualMappingCheckRan: one Bool,

    // Evidence flag recorded by EvidenceManager->AddFlagged(MANUAL_MAPPING).
    manualMappingFlagRecorded: one Bool
}

pred init[s: State] {
    s.manualMappedRegionPresent = False
    s.regionCommitted = False
    s.regionExecutable = False
    s.regionInKnownModule = False
    s.peHeaderPresent = False
    s.erasedHeaderHeuristicMatched = False
    s.manualMappingCheckRan = False
    s.manualMappingFlagRecorded = False
}

/* -------------------------
   Source-Level Detection Condition
------------------------- */

pred suspiciousManualMappedRegion[s: State] {
    s.manualMappedRegionPresent = True
    s.regionCommitted = True
    s.regionExecutable = True
    s.regionInKnownModule = False
    (s.peHeaderPresent = True or s.erasedHeaderHeuristicMatched = True)
}

/* -------------------------
   Attacker Actions
------------------------- */

// Attack Vector 1: Attacker manually maps a module and leaves a PE header.
pred mapManualModuleWithPEHeader[s, s_prime: State] {
    s_prime.manualMappedRegionPresent = True
    s_prime.regionCommitted = True
    s_prime.regionExecutable = True
    s_prime.regionInKnownModule = False
    s_prime.peHeaderPresent = True
    s_prime.erasedHeaderHeuristicMatched = False

    // Attacker action does not itself run the manual-mapping check.
    s_prime.manualMappingCheckRan = s.manualMappingCheckRan

    // No flag is recorded immediately.
    s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded
}

// Attack Vector 2: Attacker manually maps a module and erases its PE header,
// but the private executable region still matches the source heuristic.
pred mapManualModuleWithErasedHeader[s, s_prime: State] {
    s_prime.manualMappedRegionPresent = True
    s_prime.regionCommitted = True
    s_prime.regionExecutable = True
    s_prime.regionInKnownModule = False
    s_prime.peHeaderPresent = False
    s_prime.erasedHeaderHeuristicMatched = True

    // Attacker action does not itself run the manual-mapping check.
    s_prime.manualMappingCheckRan = s.manualMappingCheckRan

    // No flag is recorded immediately.
    s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded
}

/* -------------------------
   Manual Mapping Check
------------------------- */

pred checkRuns[s, s_prime: State] {
    // The periodic manual-mapping detection check runs in this step.
    s_prime.manualMappingCheckRan = True

    // Region properties persist in this abstraction.
    s_prime.manualMappedRegionPresent = s.manualMappedRegionPresent
    s_prime.regionCommitted = s.regionCommitted
    s_prime.regionExecutable = s.regionExecutable
    s_prime.regionInKnownModule = s.regionInKnownModule
    s_prime.peHeaderPresent = s.peHeaderPresent
    s_prime.erasedHeaderHeuristicMatched = s.erasedHeaderHeuristicMatched

    // If DetectManualMapping would return a suspicious region, record
    // the MANUAL_MAPPING flag. Otherwise, preserve the previous flag state.
    (suspiciousManualMappedRegion[s] and s_prime.manualMappingCheckRan = True) =>
        s_prime.manualMappingFlagRecorded = True
    else
        s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded
}

/* -------------------------
   Stutter Step
------------------------- */

pred stutter[s, s_prime: State] {
    // No action occurs in this step.
    s_prime.manualMappedRegionPresent = s.manualMappedRegionPresent
    s_prime.regionCommitted = s.regionCommitted
    s_prime.regionExecutable = s.regionExecutable
    s_prime.regionInKnownModule = s.regionInKnownModule
    s_prime.peHeaderPresent = s.peHeaderPresent
    s_prime.erasedHeaderHeuristicMatched = s.erasedHeaderHeuristicMatched
    s_prime.manualMappingCheckRan = s.manualMappingCheckRan
    s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded
}

/* -------------------------
   Step Relation
------------------------- */

pred step[s, s_prime: State] {
    mapManualModuleWithPEHeader[s, s_prime]
    or mapManualModuleWithErasedHeader[s, s_prime]
    or checkRuns[s, s_prime]
    or stutter[s, s_prime]
}

/* -------------------------
   Trace Definition
------------------------- */

fact Trace {
    init[ord/first]

    // Every non-final state transitions to the next state by one valid step.
    all s: State - ord/last | step[s, ord/next[s]]
}

/* -------------------------
   Sanity Properties
------------------------- */

/*
 * Explicit check that the trace begins in a clean state.
 */
assert InitialStateIsClean {
    init[ord/first]
}

/*
 * A MANUAL_MAPPING flag should not appear unless the manual-mapping
 * detection check has run earlier in the trace.
 */
assert NoFlagWithoutManualMappingCheck {
    all s: State |
        s.manualMappingFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.manualMappingCheckRan = True
}

/*
 * A MANUAL_MAPPING flag should not appear unless a source-detectable
 * suspicious region appeared earlier in the trace.
 */
assert NoFlagWithoutSuspiciousRegion {
    all s: State |
        s.manualMappingFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                suspiciousManualMappedRegion[p]
}

/*
 * Once a manually mapped region appears, that condition persists in this
 * abstraction.
 */
assert ManualMappedRegionMonotonic {
    all s: State - ord/last |
        s.manualMappedRegionPresent = True implies
            ord/next[s].manualMappedRegionPresent = True
}

/*
 * Once a MANUAL_MAPPING flag has been recorded, it persists.
 * This matches the abstraction of a DetectionFlags::MANUAL_MAPPING entry
 * being stored in the evidence/flag list.
 */
assert ManualMappingFlagMonotonic {
    all s: State - ord/last |
        s.manualMappingFlagRecorded = True implies
            ord/next[s].manualMappingFlagRecorded = True
}

/* -------------------------
   Main Security Properties
------------------------- */

/*
 * If a source-detectable suspicious region exists and the manual-mapping
 * detection check runs, then a MANUAL_MAPPING flag should be recorded by
 * that transition.
 */
assert SuspiciousRegionFlaggedWhenCheckRuns {
    all s: State - ord/last |
        (suspiciousManualMappedRegion[s] and checkRuns[s, ord/next[s]]) implies
            ord/next[s].manualMappingFlagRecorded = True
}

/* -------------------------
   Check Commands
------------------------- */

check InitialStateIsClean for 6
check NoFlagWithoutManualMappingCheck for 6
check NoFlagWithoutSuspiciousRegion for 6
check ManualMappedRegionMonotonic for 6
check ManualMappingFlagMonotonic for 6

check SuspiciousRegionFlaggedWhenCheckRuns for 6
