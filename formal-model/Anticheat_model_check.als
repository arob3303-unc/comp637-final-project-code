open util/ordering[State] as ord

sig State {
    -- attacker-caused bad states
    protectedSectionModified: one Bool,
    protectedSectionWritable: one Bool,

    -- anti-cheat detections
    codeIntegrityDetected: one Bool,
    pageProtectionDetected: one Bool,

    -- enforcement outcome
    flaggedCheater: one Bool
}

abstract sig Bool {}
one sig True, False extends Bool {}

pred init[s: State] {
    s.protectedSectionModified = False
    s.protectedSectionWritable = False

    s.codeIntegrityDetected = False
    s.pageProtectionDetected = False

    s.flaggedCheater = False
}

pred modifyProtectedSection[s: State, s_prime: State] {
    s_prime.protectedSectionModified = True
    s_prime.protectedSectionWritable = s.protectedSectionWritable

    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected

    s_prime.flaggedCheater = s.flaggedCheater
}

pred makeProtectedSectionWritable[s, s_prime: State] {
    s_prime.protectedSectionWritable = True
    s_prime.protectedSectionModified = s.protectedSectionModified

    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected

    s_prime.flaggedCheater = s.flaggedCheater
}
-- For first property
pred detectCodeIntegrity[s, s_prime: State] {
    s.protectedSectionModified = True

    s_prime.codeIntegrityDetected = True
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.pageProtectionDetected = s.pageProtectionDetected
    s_prime.flaggedCheater = s.flaggedCheater
}
-- for second property
pred detectPageProtection[s, s_prime: State] {
    s.protectedSectionWritable = True

    s_prime.pageProtectionDetected = True
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.flaggedCheater = s.flaggedCheater
}

pred flagAsCheater[s, s_prime: State] {
    (s.codeIntegrityDetected = True or s.pageProtectionDetected = True)

    s_prime.flaggedCheater = True
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected
}

pred stutter[s, s_prime: State] {
    s_prime.protectedSectionModified = s.protectedSectionModified
    s_prime.protectedSectionWritable = s.protectedSectionWritable
    s_prime.codeIntegrityDetected = s.codeIntegrityDetected
    s_prime.pageProtectionDetected = s.pageProtectionDetected
    s_prime.flaggedCheater = s.flaggedCheater
}

pred step[s, s_prime: State] {
    modifyProtectedSection[s, s_prime]
    or makeProtectedSectionWritable[s, s_prime]
    or detectCodeIntegrity[s, s_prime]
    or detectPageProtection[s, s_prime]
    or flagAsCheater[s, s_prime]
    or stutter[s, s_prime]
}

fact Trace {
    init[ord/first]
    all s: State - ord/last | step[s, ord/next[s]]
}

-- Assertions
assert ModifiedSectionEventuallyDetected {
    all s: State |
        s.protectedSectionModified = True implies
            some t: s.*(ord/next) | t.codeIntegrityDetected = True
}

assert WritableSectionEventuallyDetected {
    all s: State |
        s.protectedSectionWritable = True implies
            some t: s.*(ord/next) | t.pageProtectionDetected = True
}

assert DetectionEventuallyFlagged {
    all s: State |
        (s.codeIntegrityDetected = True or s.pageProtectionDetected = True) implies
            some t: s.*(ord/next) | t.flaggedCheater = True
}

check DetectionEventuallyFlagged for 6
