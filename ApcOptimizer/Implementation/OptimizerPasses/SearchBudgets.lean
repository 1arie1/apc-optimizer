set_option autoImplicit false

/-! # Search / enumeration budget constants

Representation-independent (`Nat`) runtime work caps and gates consumed by the dense passes and
their proofs. -/

/-! ## Deep byte-justification budgets -/

/-- Cap on the number of enumerated flag assignments per deep-justification attempt. -/
def maxDeepPoints : Nat := 64

/-- Cap on a single enumerated variable's domain size in the deep justification. -/
def maxDeepDomain : Nat := 4

/-- Cap on the number of candidate defining constraints tried per deep justification. -/
def maxDeepConstraints : Nat := 4

/-- Cap on a candidate constraint's number of distinct other variables (wider constraints
    cannot collapse to the ≤2-term linear shapes `pointByteOk` accepts anyway). -/
def maxDeepVars : Nat := 8

/-- Reduction fuel: how many checked forms one basis justification may subtract. -/
def basisFuel : Nat := 3

/-! ## Enumeration work caps (`DomainBatch` / `DomainFold`) -/

/-- Work cap for one joint enumeration: box size × number of covered targets. -/
def maxEnumWork : Nat := 524288

/-- From this many candidate groups on, `domainFold` uses the inverted index; below it the direct
    per-target `coveredCsOf` scan is cheaper than building the index. Gating on the group count
    rather than the system size is what makes the pass linear: the direct path costs
    `O(groups × system)`, the indexed one one build plus per-group bucket work.

    The two paths are separately proven and agree on every group they fold; they differ only in how
    much constant folding their no-op gates let through — `denseFoldRewriteV` also rewrites items
    sharing *no* variable with the group (a variable-free subexpression is vacuously `varsInF xs`),
    which the indexed path's bucket scan skips. -/
def domainFoldTargetIndexThreshold : Nat := 2

/-- Systems with at least this many bus interactions use the slot-0-indexed representative store in
    `densePdDropSet`; smaller ones scan the per-class representative list directly (the index's
    per-interaction map overhead outweighs the scan at fixture scale). Purely a runtime gate — both
    paths propose the identical drop set. -/
def pointwiseDupDropIndexThreshold : Nat := 4096
