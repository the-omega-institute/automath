import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.POM.DerivedAuditedEvenMinsectorTopologicalPhase
import Omega.Zeta.GaugeGroupTripleDecomp

namespace Omega.DerivedConsequences

/-- The audited even windows singled out by the minimum-degeneracy package. -/
def derived_foldbin_gauge_abelianization_even_windows_window : Fin 4 → ℕ
  | 0 => 6
  | 1 => 8
  | 2 => 10
  | 3 => 12

/-- The abelianization rank predicted by the foldbin gauge decomposition on an audited even
window. -/
def derived_foldbin_gauge_abelianization_even_windows_abelianization_rank (i : Fin 4) : ℕ :=
  Nat.fib (derived_foldbin_gauge_abelianization_even_windows_window i + 2)

/-- Concrete finite proxy for the abelianized gauge group: one `ZMod 2` factor for each symmetric
group factor in the audited window. -/
abbrev derived_foldbin_gauge_abelianization_even_windows_abelianization (i : Fin 4) :=
  Fin (derived_foldbin_gauge_abelianization_even_windows_abelianization_rank i) → ZMod 2

/-- The visible-character rank after removing the audited minimum-degeneracy contribution. -/
def derived_foldbin_gauge_abelianization_even_windows_visible_character_rank (i : Fin 4) : ℕ :=
  derived_foldbin_gauge_abelianization_even_windows_abelianization_rank i -
    Omega.POM.auditedEvenMinsectorDegeneracy
      (derived_foldbin_gauge_abelianization_even_windows_window i)

/-- Cardinality of the finite `(ZMod 2)^r` proxy attached to an audited even window. -/
lemma derived_foldbin_gauge_abelianization_even_windows_card (i : Fin 4) :
    Fintype.card (derived_foldbin_gauge_abelianization_even_windows_abelianization i) =
      2 ^ derived_foldbin_gauge_abelianization_even_windows_abelianization_rank i := by
  simpa [derived_foldbin_gauge_abelianization_even_windows_abelianization,
    derived_foldbin_gauge_abelianization_even_windows_abelianization_rank] using
    (Fintype.card_fun :
      Fintype.card
          (Fin (derived_foldbin_gauge_abelianization_even_windows_abelianization_rank i) →
            ZMod 2) =
        Fintype.card (ZMod 2) ^
          Fintype.card
            (Fin (derived_foldbin_gauge_abelianization_even_windows_abelianization_rank i)))

/-- The audited minimum-degeneracy values on the four even windows are exactly the corresponding
Fibonacci numbers `F_{m/2}`. -/
lemma derived_foldbin_gauge_abelianization_even_windows_audited_degeneracy (i : Fin 4) :
    Omega.POM.auditedEvenMinsectorDegeneracy
        (derived_foldbin_gauge_abelianization_even_windows_window i) =
      Nat.fib (derived_foldbin_gauge_abelianization_even_windows_window i / 2) := by
  fin_cases i <;> rfl

/-- The visible-character count is always bounded above by the full abelianization count. -/
lemma derived_foldbin_gauge_abelianization_even_windows_visible_lower_bound (i : Fin 4) :
    2 ^ (derived_foldbin_gauge_abelianization_even_windows_visible_character_rank i) ≤
      Fintype.card (derived_foldbin_gauge_abelianization_even_windows_abelianization i) := by
  rw [derived_foldbin_gauge_abelianization_even_windows_card]
  dsimp [derived_foldbin_gauge_abelianization_even_windows_visible_character_rank]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.sub_le _ _)

/-- Data wrapper for the audited even-window abelianization package. -/
structure derived_foldbin_gauge_abelianization_even_windows_data where
  auditedWindow : Fin 4

/-- Paper-facing even-window package: the audited minimum degeneracy matches the Fibonacci audit,
the abelianization is the expected `(ZMod 2)^{F_{m+2}}` proxy, the visible-character count is at
least the quotient by the audited degeneracy, and for window `6` the existing gauge split recovers
the concrete `21 = 3 + 18` lower bound. -/
def derived_foldbin_gauge_abelianization_even_windows_statement
    (D : derived_foldbin_gauge_abelianization_even_windows_data) : Prop :=
  let i := D.auditedWindow
  let m := derived_foldbin_gauge_abelianization_even_windows_window i
  let r := derived_foldbin_gauge_abelianization_even_windows_abelianization_rank i
  Omega.POM.auditedEvenMinsectorDegeneracy m = Nat.fib (m / 2) ∧
    Fintype.card (derived_foldbin_gauge_abelianization_even_windows_abelianization i) = 2 ^ r ∧
    2 ^ (derived_foldbin_gauge_abelianization_even_windows_visible_character_rank i) ≤
      Fintype.card (derived_foldbin_gauge_abelianization_even_windows_abelianization i) ∧
    (i = 0 →
      r = 21 ∧
        Omega.POM.auditedEvenMinsectorPhase m = Omega.POM.AuditedEvenMinsectorPhase.contractible ∧
        2 ^ 18 ≤ Fintype.card
          (derived_foldbin_gauge_abelianization_even_windows_abelianization i))

/-- Paper label: `thm:derived-foldbin-gauge-abelianization-even-windows`. -/
theorem paper_derived_foldbin_gauge_abelianization_even_windows
    (D : derived_foldbin_gauge_abelianization_even_windows_data) :
    derived_foldbin_gauge_abelianization_even_windows_statement D := by
  rcases Omega.POM.paper_derived_audited_even_minsector_topological_phase with
    ⟨_, _, _, _, hphase6, _, _, _⟩
  rcases D with ⟨i⟩
  fin_cases i
  · change derived_foldbin_gauge_abelianization_even_windows_statement { auditedWindow := 0 }
    refine ⟨derived_foldbin_gauge_abelianization_even_windows_audited_degeneracy 0,
      derived_foldbin_gauge_abelianization_even_windows_card 0, ?_, ?_⟩
    · exact derived_foldbin_gauge_abelianization_even_windows_visible_lower_bound 0
    · intro _
      have hsplit :=
        Omega.Zeta.GaugeGroupTripleDecomp.paper_derived_window6_gauge_center_derived_splitting
      have hvisible :
          (18 : ℕ) ≤ derived_foldbin_gauge_abelianization_even_windows_abelianization_rank 0 := by
        have htotal : (21 : ℕ) = 3 + 18 := hsplit.2.1
        have : (18 : ℕ) ≤ 21 := by omega
        have hfib8 : Nat.fib 8 = 21 := by decide
        simpa [derived_foldbin_gauge_abelianization_even_windows_abelianization_rank,
          derived_foldbin_gauge_abelianization_even_windows_window, hfib8] using this
      refine ⟨by decide, hphase6, ?_⟩
      rw [derived_foldbin_gauge_abelianization_even_windows_card 0]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hvisible
  · change derived_foldbin_gauge_abelianization_even_windows_statement { auditedWindow := 1 }
    refine ⟨derived_foldbin_gauge_abelianization_even_windows_audited_degeneracy 1,
      derived_foldbin_gauge_abelianization_even_windows_card 1, ?_, ?_⟩
    · exact derived_foldbin_gauge_abelianization_even_windows_visible_lower_bound 1
    · intro hi
      cases hi
  · change derived_foldbin_gauge_abelianization_even_windows_statement { auditedWindow := 2 }
    refine ⟨derived_foldbin_gauge_abelianization_even_windows_audited_degeneracy 2,
      derived_foldbin_gauge_abelianization_even_windows_card 2, ?_, ?_⟩
    · exact derived_foldbin_gauge_abelianization_even_windows_visible_lower_bound 2
    · intro hi
      cases hi
  · change derived_foldbin_gauge_abelianization_even_windows_statement { auditedWindow := 3 }
    refine ⟨derived_foldbin_gauge_abelianization_even_windows_audited_degeneracy 3,
      derived_foldbin_gauge_abelianization_even_windows_card 3, ?_, ?_⟩
    · exact derived_foldbin_gauge_abelianization_even_windows_visible_lower_bound 3
    · intro hi
      cases hi

end Omega.DerivedConsequences
