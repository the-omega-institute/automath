import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic
import Omega.POM.BCVisibleQuotientEventualStability

namespace Omega.POM

/-- Concrete annihilator of a BC subgroup inside the ambient character group. -/
abbrev pom_bc_anomaly_character_support_eventual_freezing_annihilator
    {G A : Type*} [CommGroup G] [CommGroup A] (N : Subgroup G) : Subgroup (G →* A) :=
  (MonoidHom.restrictHom N A).ker

/-- The anomaly support is the complement of the annihilator. -/
def pom_bc_anomaly_character_support_eventual_freezing_support
    {G A : Type*} [CommGroup G] [CommGroup A] (N : Subgroup G) : Set (G →* A) :=
  (pom_bc_anomaly_character_support_eventual_freezing_annihilator (A := A) N : Set (G →* A))ᶜ

/-- Once the BC-visible subgroup chain stabilizes, the anomaly support freezes as the complement of
the stabilized annihilator, and that annihilator is canonically the dual of the terminal visible
quotient. If the terminal subgroup is trivial, the anomaly support is empty.
    cor:pom-bc-anomaly-character-support-eventual-freezing -/
theorem paper_pom_bc_anomaly_character_support_eventual_freezing
    {G A : Type*} [CommGroup G] [Fintype G] [CommGroup A]
    (N : ℕ → Subgroup G) (hmono : ∀ m, N (m + 1) ≤ N m) :
    ∃ m0 : ℕ, ∀ m ≥ m0,
      pom_bc_anomaly_character_support_eventual_freezing_support (A := A) (N m) =
          pom_bc_anomaly_character_support_eventual_freezing_support (A := A) (N m0) ∧
        Nonempty
          (pom_bc_anomaly_character_support_eventual_freezing_annihilator (A := A) (N m0) ≃*
            (G ⧸ N m0 →* A)) ∧
        (N m0 = ⊥ →
          pom_bc_anomaly_character_support_eventual_freezing_support (A := A) (N m0) = ∅) := by
  obtain ⟨m0, hm0⟩ := paper_pom_bc_visible_quotient_eventual_stability N hmono
  refine ⟨m0, ?_⟩
  intro m hm
  have hstable : N m = N m0 := hm0 m hm
  refine ⟨?_, ?_, ?_⟩
  · simp [pom_bc_anomaly_character_support_eventual_freezing_support, hstable]
  · exact ⟨MonoidHom.restrictHomKerEquiv A (N m0)⟩
  · intro hbot
    ext χ
    simp [pom_bc_anomaly_character_support_eventual_freezing_support, hbot,
      MonoidHom.mem_ker, MonoidHom.restrict_eq_one_iff]

end Omega.POM
