import Omega.Frontier.Assumptions
import Omega.Folding.Rewrite
import Omega.Folding.Fiber
import Omega.SPG.ScanErrorDiscrete

namespace Omega.Frontier

/-- A finite certificate for a claimed global defect pattern. -/
structure DefectCertificate where
  m : Nat
  k : Nat
  input : Word (m + k)
  claimed : Word m

/-- The Lean-side verifier for a global defect certificate. -/
def DefectCertificate.Valid (c : DefectCertificate) : Prop :=
  globalDefect (Nat.le_add_right c.m c.k) c.input = c.claimed

theorem DefectCertificate.sound (c : DefectCertificate) (h : c.Valid) :
    globalDefect (Nat.le_add_right c.m c.k) c.input = c.claimed :=
  h

/-- A one-step certificate for a local defect claim. -/
structure LocalDefectCertificate where
  m : Nat
  input : Word (m + 1)
  claimed : Word m

def LocalDefectCertificate.Valid (c : LocalDefectCertificate) : Prop :=
  localDefect c.input = c.claimed

theorem LocalDefectCertificate.sound (c : LocalDefectCertificate) (h : c.Valid) :
    localDefect c.input = c.claimed :=
  h

/-- A certificate for a claimed one-step local rewrite. -/
structure RewriteStepCertificate where
  source : Rewrite.DigitCfg
  target : Rewrite.DigitCfg

/-- cert:rewrite-step -/
def RewriteStepCertificate.Valid (c : RewriteStepCertificate) : Prop :=
  Rewrite.Step c.source c.target

theorem RewriteStepCertificate.sound (c : RewriteStepCertificate) (h : c.Valid) :
    Rewrite.Step c.source c.target :=
  h

theorem RewriteStepCertificate.value_preserved (c : RewriteStepCertificate) (h : c.Valid) :
    Rewrite.value c.target = Rewrite.value c.source :=
  Rewrite.step_value h

/-- A certificate that a configuration is already rewrite-irreducible. -/
structure RewriteIrreducibleCertificate where
  source : Rewrite.DigitCfg

def RewriteIrreducibleCertificate.Valid (c : RewriteIrreducibleCertificate) : Prop :=
  Rewrite.Irreducible c.source

theorem RewriteIrreducibleCertificate.sound (c : RewriteIrreducibleCertificate) (h : c.Valid) :
    Rewrite.Irreducible c.source :=
  h

/-- A certificate for the folded image of a finite word. -/
structure FoldCertificate where
  m : Nat
  input : Word m
  claimed : X m

/-- cert:fold -/
def FoldCertificate.Valid (c : FoldCertificate) : Prop :=
  Fold c.input = c.claimed

theorem FoldCertificate.sound (c : FoldCertificate) (h : c.Valid) :
    Fold c.input = c.claimed :=
  h

theorem FoldCertificate.idempotent (c : FoldCertificate) (h : c.Valid) :
    Fold c.claimed.1 = c.claimed := by
  rw [← h]
  exact Fold_idempotent c.input

theorem FoldCertificate.inFiber (c : FoldCertificate) (h : c.Valid) :
    c.input ∈ X.fiber c.claimed := by
  rw [← h]
  exact X.mem_fiber_Fold c.input

/-- A certificate for a claimed discrete scan-error value. -/
structure ScanErrorCertificate (α β : Type*) [Fintype α] [Fintype β] where
  μ : PMF α
  obs : α → β
  event : Set α
  claimed : ENNReal

/-- cert:scan-error -/
def ScanErrorCertificate.Valid {α β : Type*} [Fintype α] [Fintype β]
    (c : ScanErrorCertificate α β) : Prop :=
  SPG.scanError c.μ c.obs c.event = c.claimed

theorem ScanErrorCertificate.sound {α β : Type*} [Fintype α] [Fintype β]
    (c : ScanErrorCertificate α β) (h : c.Valid) :
    SPG.scanError c.μ c.obs c.event = c.claimed :=
  h

/-- A certificate that an observable event has zero discrete scan error. -/
structure ObservableZeroScanCertificate (α β : Type*) [Fintype α] [Fintype β] where
  μ : PMF α
  obs : α → β
  event : Set β

def ObservableZeroScanCertificate.Valid {α β : Type*} [Fintype α] [Fintype β]
    (c : ObservableZeroScanCertificate α β) : Prop :=
  SPG.scanError c.μ c.obs (SPG.observableEvent c.obs c.event) = 0

theorem ObservableZeroScanCertificate.sound {α β : Type*} [Fintype α] [Fintype β]
    (c : ObservableZeroScanCertificate α β) (h : c.Valid) :
    SPG.scanError c.μ c.obs (SPG.observableEvent c.obs c.event) = 0 :=
  h

theorem ObservableZeroScanCertificate.canonical {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (obs : α → β) (event : Set β) :
    (ObservableZeroScanCertificate.Valid
      { μ := μ, obs := obs, event := event }) := by
  exact SPG.scanError_observableEvent_eq_zero μ obs event

/-- A prefix-resolution scan-error certificate on finite words. -/
structure PrefixScanErrorCertificate where
  m : Nat
  n : Nat
  h : m ≤ n
  μ : PMF (Word n)
  event : Set (Word n)
  claimed : ENNReal

def PrefixScanErrorCertificate.Valid (c : PrefixScanErrorCertificate) : Prop :=
  SPG.prefixScanError c.μ c.h c.event = c.claimed

theorem PrefixScanErrorCertificate.sound (c : PrefixScanErrorCertificate) (h : c.Valid) :
    SPG.prefixScanError c.μ c.h c.event = c.claimed :=
  h

/-- A prefix event certificate with guaranteed zero scan error. -/
structure PrefixZeroScanCertificate where
  m : Nat
  n : Nat
  h : m ≤ n
  μ : PMF (Word n)
  event : Set (Word m)

/-- cert:prefix-zero-scan -/
def PrefixZeroScanCertificate.Valid (c : PrefixZeroScanCertificate) : Prop :=
  SPG.prefixScanError c.μ c.h (SPG.prefixEvent c.h c.event) = 0

theorem PrefixZeroScanCertificate.sound (c : PrefixZeroScanCertificate) (h : c.Valid) :
    SPG.prefixScanError c.μ c.h (SPG.prefixEvent c.h c.event) = 0 :=
  h

theorem PrefixZeroScanCertificate.canonical {m n : Nat}
    (μ : PMF (Word n)) (h : m ≤ n) (event : Set (Word m)) :
    PrefixZeroScanCertificate.Valid
      { m := m, n := n, h := h, μ := μ, event := event } := by
  exact SPG.prefixScanError_eq_zero_of_prefixEvent μ h event

end Omega.Frontier
