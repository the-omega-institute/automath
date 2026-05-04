import Mathlib.Data.Finset.Image
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for the fold ledger: binary microstates at level `m`, a finite stable
type space, and the computable fold map from microstates to stable types. -/
structure xi_fold_algorithmic_holographic_ledger_Data where
  xi_fold_algorithmic_holographic_ledger_m : ℕ
  xi_fold_algorithmic_holographic_ledger_type : Type
  xi_fold_algorithmic_holographic_ledger_fintype :
    Fintype xi_fold_algorithmic_holographic_ledger_type
  xi_fold_algorithmic_holographic_ledger_decEq :
    DecidableEq xi_fold_algorithmic_holographic_ledger_type
  xi_fold_algorithmic_holographic_ledger_fold :
    (Fin xi_fold_algorithmic_holographic_ledger_m → Bool) →
      xi_fold_algorithmic_holographic_ledger_type

namespace xi_fold_algorithmic_holographic_ledger_Data

attribute [instance] xi_fold_algorithmic_holographic_ledger_fintype
attribute [instance] xi_fold_algorithmic_holographic_ledger_decEq

/-- Binary microstates at the audited level. -/
abbrev xi_fold_algorithmic_holographic_ledger_microstate
    (D : xi_fold_algorithmic_holographic_ledger_Data) :=
  Fin D.xi_fold_algorithmic_holographic_ledger_m → Bool

/-- The finite fiber over a stable type. -/
def xi_fold_algorithmic_holographic_ledger_fiber
    (D : xi_fold_algorithmic_holographic_ledger_Data)
    (x : D.xi_fold_algorithmic_holographic_ledger_type) :
    Finset D.xi_fold_algorithmic_holographic_ledger_microstate :=
  Finset.univ.filter fun omega =>
    D.xi_fold_algorithmic_holographic_ledger_fold omega = x

/-- Fiber multiplicity. -/
def xi_fold_algorithmic_holographic_ledger_fiberCount
    (D : xi_fold_algorithmic_holographic_ledger_Data)
    (x : D.xi_fold_algorithmic_holographic_ledger_type) : ℕ :=
  (D.xi_fold_algorithmic_holographic_ledger_fiber x).card

/-- The encoded inverse-enumeration certificate: every microstate has a rank below its fiber
count.  The rank value is represented here only by its certified range. -/
def xi_fold_algorithmic_holographic_ledger_inverseEnumeration
    (D : xi_fold_algorithmic_holographic_ledger_Data) : Prop :=
  ∀ omega : D.xi_fold_algorithmic_holographic_ledger_microstate,
    ∃ x : D.xi_fold_algorithmic_holographic_ledger_type,
      x = D.xi_fold_algorithmic_holographic_ledger_fold omega ∧
        ∃ rank : ℕ, rank < D.xi_fold_algorithmic_holographic_ledger_fiberCount x

/-- The upper complexity side of the ledger is represented by the same bounded rank code. -/
def xi_fold_algorithmic_holographic_ledger_upperComplexityBound
    (D : xi_fold_algorithmic_holographic_ledger_Data) : Prop :=
  ∀ omega : D.xi_fold_algorithmic_holographic_ledger_microstate,
    ∃ rank : ℕ,
      rank <
        D.xi_fold_algorithmic_holographic_ledger_fiberCount
          (D.xi_fold_algorithmic_holographic_ledger_fold omega)

/-- Counting lower bound: every stable type hit by the fold map has a nonempty fiber. -/
def xi_fold_algorithmic_holographic_ledger_countingLowerBound
    (D : xi_fold_algorithmic_holographic_ledger_Data) : Prop :=
  ∀ x : D.xi_fold_algorithmic_holographic_ledger_type,
    x ∈ (Finset.univ.image D.xi_fold_algorithmic_holographic_ledger_fold :
      Finset D.xi_fold_algorithmic_holographic_ledger_type) →
      0 < D.xi_fold_algorithmic_holographic_ledger_fiberCount x

/-- The finite fibers never exceed the full binary microstate space. -/
def xi_fold_algorithmic_holographic_ledger_fiberUpperBound
    (D : xi_fold_algorithmic_holographic_ledger_Data) : Prop :=
  ∀ x : D.xi_fold_algorithmic_holographic_ledger_type,
    D.xi_fold_algorithmic_holographic_ledger_fiberCount x ≤
      Fintype.card D.xi_fold_algorithmic_holographic_ledger_microstate

/-- Concrete ledger package used by the paper-facing wrapper. -/
def xi_fold_algorithmic_holographic_ledger_bounds
    (D : xi_fold_algorithmic_holographic_ledger_Data) : Prop :=
  D.xi_fold_algorithmic_holographic_ledger_inverseEnumeration ∧
    D.xi_fold_algorithmic_holographic_ledger_upperComplexityBound ∧
      D.xi_fold_algorithmic_holographic_ledger_countingLowerBound ∧
        D.xi_fold_algorithmic_holographic_ledger_fiberUpperBound

lemma xi_fold_algorithmic_holographic_ledger_mem_own_fiber
    (D : xi_fold_algorithmic_holographic_ledger_Data)
    (omega : D.xi_fold_algorithmic_holographic_ledger_microstate) :
    omega ∈
      D.xi_fold_algorithmic_holographic_ledger_fiber
        (D.xi_fold_algorithmic_holographic_ledger_fold omega) := by
  simp [xi_fold_algorithmic_holographic_ledger_fiber]

lemma xi_fold_algorithmic_holographic_ledger_fiberCount_fold_pos
    (D : xi_fold_algorithmic_holographic_ledger_Data)
    (omega : D.xi_fold_algorithmic_holographic_ledger_microstate) :
    0 <
      D.xi_fold_algorithmic_holographic_ledger_fiberCount
        (D.xi_fold_algorithmic_holographic_ledger_fold omega) := by
  exact Finset.card_pos.mpr
    ⟨omega, D.xi_fold_algorithmic_holographic_ledger_mem_own_fiber omega⟩

lemma xi_fold_algorithmic_holographic_ledger_rank_certificate
    (D : xi_fold_algorithmic_holographic_ledger_Data)
    (omega : D.xi_fold_algorithmic_holographic_ledger_microstate) :
    ∃ rank : ℕ,
      rank <
        D.xi_fold_algorithmic_holographic_ledger_fiberCount
          (D.xi_fold_algorithmic_holographic_ledger_fold omega) := by
  exact ⟨0, D.xi_fold_algorithmic_holographic_ledger_fiberCount_fold_pos omega⟩

end xi_fold_algorithmic_holographic_ledger_Data

open xi_fold_algorithmic_holographic_ledger_Data

/-- Paper label: `thm:xi-fold-algorithmic-holographic-ledger`. -/
theorem paper_xi_fold_algorithmic_holographic_ledger
    (D : xi_fold_algorithmic_holographic_ledger_Data) :
    D.xi_fold_algorithmic_holographic_ledger_bounds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro omega
    refine ⟨D.xi_fold_algorithmic_holographic_ledger_fold omega, rfl, ?_⟩
    exact D.xi_fold_algorithmic_holographic_ledger_rank_certificate omega
  · intro omega
    exact D.xi_fold_algorithmic_holographic_ledger_rank_certificate omega
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨omega, _homega, rfl⟩
    exact D.xi_fold_algorithmic_holographic_ledger_fiberCount_fold_pos omega
  · intro x
    exact Finset.card_le_univ _

end Omega.Zeta
