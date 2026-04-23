/* Anticheat Model Check - FOR integrity (content tampering) and writable detection (page protection violations) */

// Use temporal logic module for "always" and "eventually" properties
// We use 'ord' to refer to ordering functions (first, next, last)
open util/ordering[State] as ord

// 1. SIGNATURES: Define variables representing the system state
sig State {
    // ----- Attacker-Caused Bad States -----
    // Has the protected section been modified?
    protectedSectionModified: one Bool,
    // Did attacker make protected section writable?
    protectedSectionWritable: one Bool,

    // ----- Periodic Check State / Integrity Subsystem -----
    integrityCheckRan: one Bool, // Whether the code integrity check has run in this state
    codeIntegrityViolationRecorded: one Bool, // Was a code integrity violation recorded?
    pageProtectionViolationRecorded: one Bool, // Was a page protection violation recorded?

    // ----- Anti-Cheat Escalation State -----
    codeIntegrityDetected: one Bool, // Has the code integrity violation been escalated into an anti cheat detection outcome?
    pageProtectionDetected: one Bool, // Has the page protection violation been escalated into an anti cheat detection outcome?

    // ----- Enforcement Outcome ----- -> important for final property
    // if any detection is raised but the player is not flagged, that would be a failure of the system
    // so, this would cause a counterexample to be generated, showing a trace where detection happens but enforcement does not.
    flaggedCheater: one Bool // This represents whether the player has been flagged as a cheater (enforcement action taken)
}

// Define abstract Bool type with two concrete instances: True and False
abstract sig Bool {}
one sig True, False extends Bool {}

// 2. INITIAL STATE
// All variables start as False - the system begins in a clean state
pred init[s: State] {
    s.protectedSectionModified = False
    s.protectedSectionWritable = False

    s.integrityCheckRan = False
    s.codeIntegrityViolationRecorded = False
    s.pageProtectionViolationRecorded = False

    s.codeIntegrityDetected = False
    s.pageProtectionDetected = False

    s.flaggedCheater = False
}

// 3. TRANSITIONS: Attacker Actions
// Attack Vector 1: Attacker modifies protected code (.text section)
pred modifyProtectedSection[s: State, s_prime: State] {
    // Attacker successfully modifies the protected section
    s_prime.protectedSectionModified = True
    // Writable status remains unchanged
    s_prime.protectedSectionWritable = s.protectedSectionWritable

    s_prime.integrityCheckRan = s.integrityCheckRan // Attacker action does not itself run the integrity thread

    // No violation is automatically recorded at the instant of attack
    s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded 
    s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded 

    // No detections happen yet (attacker hasn't been caught)
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected

    // Player hasn't been flagged yet
    s_prime.flaggedCheater = s.flaggedCheater
}

// Attack Vector 2: Attacker makes protected section writable
// (Changing page protections is often the first step before modifying code)
pred makeProtectedSectionWritable[s, s_prime: State] {
    // Attacker changes page protections to make section writable
    s_prime.protectedSectionWritable = True
    // Modified status remains unchanged
    s_prime.protectedSectionModified = s.protectedSectionModified

    s_prime.integrityCheckRan = s.integrityCheckRan // Attacker action does not itself run the integrity thread

    // No violations are automatically recorded at the instant of attack
    s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded
    s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded

    // No detections is automatically escalated yet
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected

    // Player hasn't been flagged yet
    s_prime.flaggedCheater = s.flaggedCheater
}


// PERIODIC INTEGRITY CHECK
pred runPeriodicIntegrityCheck[s: State, s_prime: State] {
    // The integrity check thread has run
    s_prime.integrityCheckRan = True

    // Attacker-caused bad states persist unless changed elsewhere
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable

    // Record code-integrity violation if modification is present
    s.protectedSectionModified = True
        => s_prime.codeIntegrityViolationRecorded = True
        else s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded

    // Record page-protection violation if writability is present
    s.protectedSectionWritable = True
        => s_prime.pageProtectionViolationRecorded = True
        else s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded

    // Running the integrity thread does not itself force escalation
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected

    // Running the integrity thread does not itself force enforcement
    s_prime.flaggedCheater = s.flaggedCheater
}

// Escalation Transitions
// Escalation Channel 1: Code integrity violation is detected and escalated
pred escalateCodeIntegrityViolation[s: State, s_prime: State] {
    // Precondition: the integrity subsytem already recorded the violation
    s.codeIntegrityViolationRecorded = True
    // Effect: raise code integrity detection
    s_prime.codeIntegrityDetected = True

    // Carry over all other state properties
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.integrityCheckRan = s.integrityCheckRan
    s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded
    s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded
    s_prime.pageProtectionDetected = s.pageProtectionDetected
    s_prime.flaggedCheater = s.flaggedCheater
}

// Escalation Channel 2: Page protection violation is detected and escalated
pred escalatePageProtectionViolation[s: State, s_prime: State] {
    // Precondition: the integrity subsytem already recored the violation
    s.pageProtectionViolationRecorded = True
    // Effect: raise page protection detection
    s_prime.pageProtectionDetected = True

    // Carry over all other state properties
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.integrityCheckRan = s.integrityCheckRan
    s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded
    s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.flaggedCheater = s.flaggedCheater
}

// 5. TRANSITIONS: Enforcement Action
// Flag the player as a cheater if ANY detection triggered
pred flagAsCheater[s, s_prime: State] {
    // PRECONDITION: Can only flag if at least one detection has been raised
    (s.codeIntegrityDetected = True or s.pageProtectionDetected = True)

    // EFFECT: Player is flagged
    s_prime.flaggedCheater = True
    // Attack/detection status remains unchanged
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.integrityCheckRan = s.integrityCheckRan
    s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded
    s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected
}

// 6. SANITY CHECK: Stutter Predicate
// Allow state to transition to itself (no action taken)
// Critical for temporal logic - prevents artificial violations
pred stutter[s, s_prime: State] {
    // All properties remain unchanged
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.integrityCheckRan = s.integrityCheckRan
    s_prime.codeIntegrityViolationRecorded = s.codeIntegrityViolationRecorded
    s_prime.pageProtectionViolationRecorded = s.pageProtectionViolationRecorded
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected
    s_prime.flaggedCheater = s.flaggedCheater
}

// 7. MASTER TRANSITION PREDICATE
// Defines what a single step in the system can do
// A step is ANY ONE of: attack, detect, enforce, or do nothing (stutter)
pred step[s, s_prime: State] {
    modifyProtectedSection[s, s_prime]
    or makeProtectedSectionWritable[s, s_prime]
    or runPeriodicIntegrityCheck[s, s_prime]
    or escalateCodeIntegrityViolation[s, s_prime]
    or escalatePageProtectionViolation[s, s_prime]
    or flagAsCheater[s, s_prime]
    or stutter[s, s_prime]
}

// 8. SYSTEM DYNAMICS: The Complete Trace
// This defines the full execution path for all states
fact Trace {
    // Start with the initial state
    init[ord/first]
    // Every state (except the last) must transition to the next via 'step'
    all s: State - ord/last | step[s, ord/next[s]]
}

// 9. Sanity Check Properties
// Ensure the system behaves as expected when not under attack

// Explicitly checking that initial state is clean
assert InitialStateIsClean {
    init[ord/first]
}

assert NoCodeViolationWithoutIntegrityCheck {
    all s: State |
        s.codeIntegrityViolationRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.integrityCheckRan = True
}

assert NoPageViolationWithoutIntegrityCheck {
    all s: State |
        s.pageProtectionViolationRecorded = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.integrityCheckRan = True
}

assert NoCodeIntegrityDetectionWithoutRecordedViolation {
    all s: State |
        s.codeIntegrityDetected = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.codeIntegrityViolationRecorded = True
}

assert NoPageProtectionDetectionWithoutRecordedViolation {
    all s: State |
        s.pageProtectionDetected = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.pageProtectionViolationRecorded = True
}
assert NoFlagWithoutDetection {
    all s: State |
        s.flaggedCheater = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.codeIntegrityDetected = True or p.pageProtectionDetected = True
}

assert FlaggingMonotonic {
    all s: State - ord/last |
        s.flaggedCheater = True implies ord/next[s].flaggedCheater = True
}
// 10. SECURITY PROPERTIES: Three Assertions to Verify
// ===================================================

// ASSERTION 1: Code modification must eventually be detected
// If the protected section is modified, the periodic integrity check should eventually record a code integrity violation
assert ModifiedSectionEventuallyRecorded {
    all s: State |
        s.protectedSectionModified = True implies
            some t: s.*(ord/next) | t.codeIntegrityViolationRecorded = True
}


// ASSERTION 2: Page protection violation must eventually be detected
// If the protected section becomes writable, the periodic integrity check should eventually record a page protection violation
assert WritableSectionEventuallyRecorded {
    all s: State |
        s.protectedSectionWritable = True implies
            some t: s.*(ord/next) | t.pageProtectionViolationRecorded = True
}

// ASSERTION 3: If a code integrity violation has been recorded, it should eventually be escalated into an anti-cheat dection result
assert CodeViolationEventuallyEscalated {
    all s: State |
        s.codeIntegrityViolationRecorded = True implies
            some t: s.*(ord/next) | t.codeIntegrityDetected = True
}

// ASSERTION 4: If a page protection violation has been recorded, it should eventually be escalated into an anti-cheat detection result
assert PageViolationEventuallyEscalated {
    all s: State |
        s.pageProtectionViolationRecorded = True implies
            some t: s.*(ord/next) | t.pageProtectionDetected = True
}

// ASSERTION 3: Detection must eventually lead to enforcement
// If ANY detection fires, the player MUST eventually be flagged
// This is the most important property - it ensures detections lead to action
assert DetectionEventuallyFlagged {
    all s: State |
        (s.codeIntegrityDetected = True or s.pageProtectionDetected = True) implies
            some t: s.*(ord/next) | t.flaggedCheater = True
}

-- Sanity checks
check InitialStateIsClean for 6
check NoCodeViolationWithoutIntegrityCheck for 6
check NoPageViolationWithoutIntegrityCheck for 6
check NoCodeIntegrityDetectionWithoutRecordedViolation for 6
check NoPageProtectionDetectionWithoutRecordedViolation for 6
check NoFlagWithoutDetection for 6
check FlaggingMonotonic for 6

-- Main security properties
check ModifiedSectionEventuallyRecorded for 6
check WritableSectionEventuallyRecorded for 6
check CodeViolationEventuallyEscalated for 6
check PageViolationEventuallyEscalated for 6
check DetectionEventuallyFlagged for 6