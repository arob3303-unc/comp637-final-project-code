/* Anticheat Model Check - FOR integrity (content tampering) and writable detection (page protection violations) */

// Use temporal logic module for "always" and "eventually" properties
// We use 'ord' to refer to ordering functions (first, next, last)
open util/ordering[State] as ord

// 1. SIGNATURES: Define variables representing the system state
sig State {
    // ----- Attacker-Caused Bad States -----
    // Did attacker modify the protected .text section?
    protectedSectionModified: one Bool,
    // Did attacker make protected section writable?
    protectedSectionWritable: one Bool,

    // ----- Anti-Cheat Detections (Separate Channels) -----
    // Did we detect code integrity violation?
    codeIntegrityDetected: one Bool,
    // Did we detect page protection violation?
    pageProtectionDetected: one Bool,

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

    // No detections happen yet
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected

    // Player hasn't been flagged yet
    s_prime.flaggedCheater = s.flaggedCheater
}

// 4. TRANSITIONS: Anti-Cheat Detection Actions
// Detection Channel 1: Code integrity check
// This represents the anti-cheat scanning for .text section modifications
pred detectCodeIntegrity[s, s_prime: State] {
    // PRECONDITION: Code integrity check can only detect if section was modified
    s.protectedSectionModified = True

    // EFFECT: Detection flag is raised
    s_prime.codeIntegrityDetected = True
    // Other properties carry over unchanged
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.pageProtectionDetected = s.pageProtectionDetected
    s_prime.flaggedCheater = s.flaggedCheater
}

// Detection Channel 2: Page protection check
// This represents the anti-cheat scanning for writable protected pages
pred detectPageProtection[s, s_prime: State] {
    // PRECONDITION: Page protection check can only detect if section became writable
    s.protectedSectionWritable = True

    // EFFECT: Detection flag is raised
    s_prime.pageProtectionDetected = True
    // Other properties carry over unchanged
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
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
    or detectCodeIntegrity[s, s_prime]
    or detectPageProtection[s, s_prime]
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

assert NoFlagWithoutDetection {
    all s: State |
        s.flaggedCheater = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.codeIntegrityDetected = True or p.pageProtectionDetected = True
}

assert NoCodeIntegrityFalsePositive {
    all s: State |
        s.codeIntegrityDetected = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
            p.protectedSectionModified = True
}

assert NoPageProtectionFalsePositive {
    all s: State |
        s.pageProtectionDetected = True implies
            some p: ord/first.*(ord/next) & s.*(~ord/next) |
                p.protectedSectionWritable = True
}

assert FlaggingMonotonic {
    all s: State - ord/last |
        s.flaggedCheater = True implies ord/next[s].flaggedCheater = True
}
// 10. SECURITY PROPERTIES: Three Assertions to Verify
// ===================================================

// ASSERTION 1: Code modification must eventually be detected
// If an attacker modifies code, the anti-cheat MUST catch it
assert ModifiedSectionEventuallyDetected {
    all s: State |
        s.protectedSectionModified = True implies
            some t: s.*(ord/next) | t.codeIntegrityDetected = True
}

// ASSERTION 2: Page protection violation must eventually be detected
// If an attacker makes pages writable, the anti-cheat MUST catch it
assert WritableSectionEventuallyDetected {
    all s: State |
        s.protectedSectionWritable = True implies
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

// 10. VERIFICATION: Check the strongest assertion
check InitialStateIsClean for 6
check NoFlagWithoutDetection for 6
check NoCodeIntegrityFalsePositive for 6
check NoPageProtectionFalsePositive for 6
check FlaggingMonotonic for 6

check ModifiedSectionEventuallyDetected for 6
check WritableSectionEventuallyDetected for 6

// We check DetectionEventuallyFlagged with scope 6 States
// This verifies the complete chain: Attack → Detection → Enforcement
check DetectionEventuallyFlagged for 6
