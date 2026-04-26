/*
 * anti_cheat_model_combined.als
 *
 * Combined source-faithful model of the anti-cheat detection mechanisms
 * covered by:
 *
 *   checksum_integrity.als
 *   debugger-model.als
 *   manual_mapping.als
 *   page_protections.als
 *   tls_integrity.als
 *
 * Source-level structure:
 *
 *   - Integrity::PeriodicIntegrityCheck records internal checksum violations.
 *   - AntiDebug::CheckForDebugger records debugger DetectionFlags.
 *   - Detections::Monitor records TLS CODE_INTEGRITY, MANUAL_MAPPING, and
 *     PAGE_PROTECTIONS flags during its periodic monitor loop.
 *
 * As in the separate models, this file does not assume scheduler fairness.
 * The main properties say that if the relevant bad condition is present and
 * the corresponding source check runs, then the relevant violation/flag is
 * recorded by that transition.
 */

open util/ordering[State] as ord

abstract sig Bool {}
one sig True, False extends Bool {}

sig State {
    /* Checksum integrity: Integrity::PeriodicIntegrityCheck */
    protectedSectionModified: one Bool,
    checksumCheckRan: one Bool,
    checksumViolationRecorded: one Bool,

    /* Debugger detection: AntiDebug::CheckForDebugger */
    debuggerAttached: one Bool,
    debuggerCheckRan: one Bool,
    debuggerDetectionRecorded: one Bool,

    /* Manual mapping: Detections::DetectManualMapping */
    manualMappedRegionPresent: one Bool,
    regionCommitted: one Bool,
    regionExecutable: one Bool,
    regionInKnownModule: one Bool,
    peHeaderPresent: one Bool,
    erasedHeaderHeuristicMatched: one Bool,
    manualMappingCheckRan: one Bool,
    manualMappingFlagRecorded: one Bool,

    /* Page protections: Detections::FindWritableAddress in release builds */
    protectedSectionWritable: one Bool,
    pageProtectionCheckRan: one Bool,
    pageProtectionFlagRecorded: one Bool,

    /* TLS integrity: Integrity::IsTLSCallbackStructureModified */
    tlsCallbackModified: one Bool,
    tlsIntegrityCheckRan: one Bool,
    tlsCodeIntegrityFlagRecorded: one Bool
}

/* -------------------------
   Initial State
------------------------- */

pred init[s: State] {
    s.protectedSectionModified = False
    s.checksumCheckRan = False
    s.checksumViolationRecorded = False

    s.debuggerAttached = False
    s.debuggerCheckRan = False
    s.debuggerDetectionRecorded = False

    s.manualMappedRegionPresent = False
    s.regionCommitted = False
    s.regionExecutable = False
    s.regionInKnownModule = False
    s.peHeaderPresent = False
    s.erasedHeaderHeuristicMatched = False
    s.manualMappingCheckRan = False
    s.manualMappingFlagRecorded = False

    s.protectedSectionWritable = False
    s.pageProtectionCheckRan = False
    s.pageProtectionFlagRecorded = False

    s.tlsCallbackModified = False
    s.tlsIntegrityCheckRan = False
    s.tlsCodeIntegrityFlagRecorded = False
}

/* -------------------------
   Frame Predicates
------------------------- */

pred unchangedChecksum[s, s_prime: State] {
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.checksumCheckRan = s.checksumCheckRan
    s_prime.checksumViolationRecorded = s.checksumViolationRecorded
}

pred unchangedDebugger[s, s_prime: State] {
    s_prime.debuggerAttached = s.debuggerAttached
    s_prime.debuggerCheckRan = s.debuggerCheckRan
    s_prime.debuggerDetectionRecorded = s.debuggerDetectionRecorded
}

pred unchangedManualMapping[s, s_prime: State] {
    s_prime.manualMappedRegionPresent = s.manualMappedRegionPresent
    s_prime.regionCommitted = s.regionCommitted
    s_prime.regionExecutable = s.regionExecutable
    s_prime.regionInKnownModule = s.regionInKnownModule
    s_prime.peHeaderPresent = s.peHeaderPresent
    s_prime.erasedHeaderHeuristicMatched = s.erasedHeaderHeuristicMatched
    s_prime.manualMappingCheckRan = s.manualMappingCheckRan
    s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded
}

pred unchangedPageProtections[s, s_prime: State] {
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.pageProtectionCheckRan = s.pageProtectionCheckRan
    s_prime.pageProtectionFlagRecorded = s.pageProtectionFlagRecorded
}

pred unchangedTLSIntegrity[s, s_prime: State] {
    s_prime.tlsCallbackModified = s.tlsCallbackModified
    s_prime.tlsIntegrityCheckRan = s.tlsIntegrityCheckRan
    s_prime.tlsCodeIntegrityFlagRecorded = s.tlsCodeIntegrityFlagRecorded
}

pred unchangedAll[s, s_prime: State] {
    unchangedChecksum[s, s_prime]
    unchangedDebugger[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

/* -------------------------
   Source-Level Detection Conditions
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

// Attack Vector 1: attacker modifies a protected non-writable code/data section.
pred modifyProtectedSection[s, s_prime: State] {
    s_prime.protectedSectionModified = True
    s_prime.checksumCheckRan = s.checksumCheckRan
    s_prime.checksumViolationRecorded = s.checksumViolationRecorded

    unchangedDebugger[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// Attack Vector 2: attacker attaches a debugger or creates a debugger-present condition.
pred attachDebugger[s, s_prime: State] {
    s_prime.debuggerAttached = True
    s_prime.debuggerCheckRan = s.debuggerCheckRan
    s_prime.debuggerDetectionRecorded = s.debuggerDetectionRecorded

    unchangedChecksum[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// Attack Vector 3a: attacker manually maps a module and leaves its PE header.
pred mapManualModuleWithPEHeader[s, s_prime: State] {
    s_prime.manualMappedRegionPresent = True
    s_prime.regionCommitted = True
    s_prime.regionExecutable = True
    s_prime.regionInKnownModule = False
    s_prime.peHeaderPresent = True
    s_prime.erasedHeaderHeuristicMatched = False
    s_prime.manualMappingCheckRan = s.manualMappingCheckRan
    s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded

    unchangedChecksum[s, s_prime]
    unchangedDebugger[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// Attack Vector 3b: attacker erases the PE header, but the private executable
// region still matches the source heuristic for a possible section.
pred mapManualModuleWithErasedHeader[s, s_prime: State] {
    s_prime.manualMappedRegionPresent = True
    s_prime.regionCommitted = True
    s_prime.regionExecutable = True
    s_prime.regionInKnownModule = False
    s_prime.peHeaderPresent = False
    s_prime.erasedHeaderHeuristicMatched = True
    s_prime.manualMappingCheckRan = s.manualMappingCheckRan
    s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded

    unchangedChecksum[s, s_prime]
    unchangedDebugger[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// Attack Vector 4: attacker makes the protected .text-style section writable.
pred makeProtectedSectionWritable[s, s_prime: State] {
    s_prime.protectedSectionWritable = True
    s_prime.pageProtectionCheckRan = s.pageProtectionCheckRan
    s_prime.pageProtectionFlagRecorded = s.pageProtectionFlagRecorded

    unchangedChecksum[s, s_prime]
    unchangedDebugger[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// Attack Vector 5: attacker modifies TLS callback structure/data.
pred modifyTLSCallbackStructure[s, s_prime: State] {
    s_prime.tlsCallbackModified = True
    s_prime.tlsIntegrityCheckRan = s.tlsIntegrityCheckRan
    s_prime.tlsCodeIntegrityFlagRecorded = s.tlsCodeIntegrityFlagRecorded

    unchangedChecksum[s, s_prime]
    unchangedDebugger[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedPageProtections[s, s_prime]
}

/* -------------------------
   Source Check Transitions
------------------------- */

// Integrity::PeriodicIntegrityCheck recomputes section checksums and records
// internal IntegrityViolation entries. In the current source, these checksum
// violations are internal to Integrity rather than directly added to EvidenceLocker.
pred checksumCheckRuns[s, s_prime: State] {
    s_prime.checksumCheckRan = True
    s_prime.protectedSectionModified = s.protectedSectionModified

    (s.protectedSectionModified = True and s_prime.checksumCheckRan = True) =>
        s_prime.checksumViolationRecorded = True
    else
        s_prime.checksumViolationRecorded = s.checksumViolationRecorded

    unchangedDebugger[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// AntiDebug::CheckForDebugger runs independently from the main monitor loop.
// debuggerDetectionRecorded abstracts any non-NONE DEBUG_* DetectionFlags result.
pred debuggerCheckRuns[s, s_prime: State] {
    s_prime.debuggerCheckRan = True
    s_prime.debuggerAttached = s.debuggerAttached

    (s.debuggerAttached = True and s_prime.debuggerCheckRan = True) =>
        s_prime.debuggerDetectionRecorded = True
    else
        s_prime.debuggerDetectionRecorded = s.debuggerDetectionRecorded

    unchangedChecksum[s, s_prime]
    unchangedManualMapping[s, s_prime]
    unchangedPageProtections[s, s_prime]
    unchangedTLSIntegrity[s, s_prime]
}

// Detections::Monitor checks TLS integrity, manual mapping, and page
// protections in one periodic monitor loop iteration.
pred monitorCheckRuns[s, s_prime: State] {
    s_prime.manualMappingCheckRan = True
    s_prime.pageProtectionCheckRan = True
    s_prime.tlsIntegrityCheckRan = True

    s_prime.manualMappedRegionPresent = s.manualMappedRegionPresent
    s_prime.regionCommitted = s.regionCommitted
    s_prime.regionExecutable = s.regionExecutable
    s_prime.regionInKnownModule = s.regionInKnownModule
    s_prime.peHeaderPresent = s.peHeaderPresent
    s_prime.erasedHeaderHeuristicMatched = s.erasedHeaderHeuristicMatched

    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.tlsCallbackModified = s.tlsCallbackModified

    suspiciousManualMappedRegion[s] =>
        s_prime.manualMappingFlagRecorded = True
    else
        s_prime.manualMappingFlagRecorded = s.manualMappingFlagRecorded

    (s.protectedSectionWritable = True and s_prime.pageProtectionCheckRan = True) =>
        s_prime.pageProtectionFlagRecorded = True
    else
        s_prime.pageProtectionFlagRecorded = s.pageProtectionFlagRecorded

    (s.tlsCallbackModified = True and s_prime.tlsIntegrityCheckRan = True) =>
        s_prime.tlsCodeIntegrityFlagRecorded = True
    else
        s_prime.tlsCodeIntegrityFlagRecorded = s.tlsCodeIntegrityFlagRecorded

    unchangedChecksum[s, s_prime]
    unchangedDebugger[s, s_prime]
}

/* -------------------------
   Stutter Step
------------------------- */

pred stutter[s, s_prime: State] {
    // No action occurs in this step.
    unchangedAll[s, s_prime]
}

/* -------------------------
   Step Relation
------------------------- */

pred step[s, s_prime: State] {
    modifyProtectedSection[s, s_prime]
    or attachDebugger[s, s_prime]
    or mapManualModuleWithPEHeader[s, s_prime]
    or mapManualModuleWithErasedHeader[s, s_prime]
    or makeProtectedSectionWritable[s, s_prime]
    or modifyTLSCallbackStructure[s, s_prime]
    or checksumCheckRuns[s, s_prime]
    or debuggerCheckRuns[s, s_prime]
    or monitorCheckRuns[s, s_prime]
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

assert InitialStateIsClean {
    init[ord/first]
}

assert NoChecksumViolationWithoutChecksumCheck {
    all s: State |
        s.checksumViolationRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.checksumCheckRan = True
}

assert NoChecksumViolationWithoutModification {
    all s: State |
        s.checksumViolationRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.protectedSectionModified = True
}

assert NoDebuggerDetectionWithoutDebuggerCheck {
    all s: State |
        s.debuggerDetectionRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.debuggerCheckRan = True
}

assert NoDebuggerDetectionWithoutDebuggerAttachment {
    all s: State |
        s.debuggerDetectionRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.debuggerAttached = True
}

assert NoManualMappingFlagWithoutManualMappingCheck {
    all s: State |
        s.manualMappingFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.manualMappingCheckRan = True
}

assert NoManualMappingFlagWithoutSuspiciousRegion {
    all s: State |
        s.manualMappingFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                suspiciousManualMappedRegion[p]
}

assert NoPageProtectionFlagWithoutPageProtectionCheck {
    all s: State |
        s.pageProtectionFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.pageProtectionCheckRan = True
}

assert NoPageProtectionFlagWithoutWritableSection {
    all s: State |
        s.pageProtectionFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.protectedSectionWritable = True
}

assert NoTLSCodeIntegrityFlagWithoutTLSCheck {
    all s: State |
        s.tlsCodeIntegrityFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.tlsIntegrityCheckRan = True
}

assert NoTLSCodeIntegrityFlagWithoutTLSModification {
    all s: State |
        s.tlsCodeIntegrityFlagRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.tlsCallbackModified = True
}

/* -------------------------
   Monotonicity Properties
------------------------- */

assert BadStatesMonotonic {
    all s: State - ord/last |
        (s.protectedSectionModified = True implies ord/next[s].protectedSectionModified = True)
        and (s.debuggerAttached = True implies ord/next[s].debuggerAttached = True)
        and (s.manualMappedRegionPresent = True implies ord/next[s].manualMappedRegionPresent = True)
        and (s.protectedSectionWritable = True implies ord/next[s].protectedSectionWritable = True)
        and (s.tlsCallbackModified = True implies ord/next[s].tlsCallbackModified = True)
}

assert DetectionRecordsMonotonic {
    all s: State - ord/last |
        (s.checksumViolationRecorded = True implies ord/next[s].checksumViolationRecorded = True)
        and (s.debuggerDetectionRecorded = True implies ord/next[s].debuggerDetectionRecorded = True)
        and (s.manualMappingFlagRecorded = True implies ord/next[s].manualMappingFlagRecorded = True)
        and (s.pageProtectionFlagRecorded = True implies ord/next[s].pageProtectionFlagRecorded = True)
        and (s.tlsCodeIntegrityFlagRecorded = True implies ord/next[s].tlsCodeIntegrityFlagRecorded = True)
}

/* -------------------------
   Main Security Properties
------------------------- */

assert ModifiedSectionRecordedWhenChecksumCheckRuns {
    all s: State - ord/last |
        (s.protectedSectionModified = True and checksumCheckRuns[s, ord/next[s]]) implies
            ord/next[s].checksumViolationRecorded = True
}

assert DebuggerAttachmentDetectedWhenDebuggerCheckRuns {
    all s: State - ord/last |
        (s.debuggerAttached = True and debuggerCheckRuns[s, ord/next[s]]) implies
            ord/next[s].debuggerDetectionRecorded = True
}

assert SuspiciousManualMappingFlaggedWhenMonitorRuns {
    all s: State - ord/last |
        (suspiciousManualMappedRegion[s] and monitorCheckRuns[s, ord/next[s]]) implies
            ord/next[s].manualMappingFlagRecorded = True
}

assert WritableSectionFlaggedWhenMonitorRuns {
    all s: State - ord/last |
        (s.protectedSectionWritable = True and monitorCheckRuns[s, ord/next[s]]) implies
            ord/next[s].pageProtectionFlagRecorded = True
}

assert TLSModificationFlaggedWhenMonitorRuns {
    all s: State - ord/last |
        (s.tlsCallbackModified = True and monitorCheckRuns[s, ord/next[s]]) implies
            ord/next[s].tlsCodeIntegrityFlagRecorded = True
}

/* -------------------------
   Check Commands
------------------------- */

check InitialStateIsClean for 6

check NoChecksumViolationWithoutChecksumCheck for 6
check NoChecksumViolationWithoutModification for 6
check NoDebuggerDetectionWithoutDebuggerCheck for 6
check NoDebuggerDetectionWithoutDebuggerAttachment for 6
check NoManualMappingFlagWithoutManualMappingCheck for 6
check NoManualMappingFlagWithoutSuspiciousRegion for 6
check NoPageProtectionFlagWithoutPageProtectionCheck for 6
check NoPageProtectionFlagWithoutWritableSection for 6
check NoTLSCodeIntegrityFlagWithoutTLSCheck for 6
check NoTLSCodeIntegrityFlagWithoutTLSModification for 6

check BadStatesMonotonic for 6
check DetectionRecordsMonotonic for 6

check ModifiedSectionRecordedWhenChecksumCheckRuns for 6
check DebuggerAttachmentDetectedWhenDebuggerCheckRuns for 6
check SuspiciousManualMappingFlaggedWhenMonitorRuns for 6
check WritableSectionFlaggedWhenMonitorRuns for 6
check TLSModificationFlaggedWhenMonitorRuns for 6
