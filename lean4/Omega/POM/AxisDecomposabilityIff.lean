import Mathlib

namespace Omega.POM

open Finset
open scoped BigOperators

/-- Inclusion-exclusion higher cross anomaly used by the axis-decomposability audit.
    `thm:pom-axis-decomposability-iff` -/
def pom_axis_decomposability_iff_higher_cross_anomaly {k : Nat}
    (L : Finset (Fin k) → ℝ) (S : Finset (Fin k)) : ℝ :=
  Finset.sum S.powerset fun T => (-1 : ℝ) ^ (S.card - T.card) * L T

lemma pom_axis_decomposability_iff_higher_cross_anomaly_insert {k : Nat}
    (L : Finset (Fin k) → ℝ) {a : Fin k} {S : Finset (Fin k)} (ha : a ∉ S) :
    pom_axis_decomposability_iff_higher_cross_anomaly L (insert a S) =
      pom_axis_decomposability_iff_higher_cross_anomaly
        (fun T => L (insert a T) - L T) S := by
  classical
  rw [pom_axis_decomposability_iff_higher_cross_anomaly]
  rw [Finset.sum_powerset_insert ha]
  rw [pom_axis_decomposability_iff_higher_cross_anomaly]
  have hfirst :
      Finset.sum S.powerset
          (fun t => (-1 : ℝ) ^ ((insert a S).card - t.card) * L t) =
        -Finset.sum S.powerset (fun t => (-1 : ℝ) ^ (S.card - t.card) * L t) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊆ S := Finset.mem_powerset.mp hT
    have hle : T.card ≤ S.card := Finset.card_le_card hsub
    have hcard : (insert a S).card - T.card = (S.card - T.card) + 1 := by
      rw [Finset.card_insert_of_notMem ha]
      omega
    rw [hcard, pow_succ]
    ring
  have hsecond :
      Finset.sum S.powerset
          (fun t => (-1 : ℝ) ^ ((insert a S).card - (insert a t).card) *
            L (insert a t)) =
        Finset.sum S.powerset
          (fun t => (-1 : ℝ) ^ (S.card - t.card) * L (insert a t)) := by
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊆ S := Finset.mem_powerset.mp hT
    have haT : a ∉ T := fun h => ha (hsub h)
    have hle : T.card ≤ S.card := Finset.card_le_card hsub
    have hcard : (insert a S).card - (insert a T).card = S.card - T.card := by
      rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haT]
      omega
    rw [hcard]
  rw [hfirst, hsecond]
  simp only [mul_sub, Finset.sum_sub_distrib]
  abel

lemma pom_axis_decomposability_iff_mobius_inversion {k : Nat}
    (L : Finset (Fin k) → ℝ) :
    ∀ S : Finset (Fin k),
      L S = Finset.sum S.powerset
        (fun T => pom_axis_decomposability_iff_higher_cross_anomaly L T) := by
  classical
  intro S
  induction S using Finset.induction_on generalizing L with
  | empty =>
      simp [pom_axis_decomposability_iff_higher_cross_anomaly]
  | insert a S ha ih =>
      let D : Finset (Fin k) → ℝ := fun T => L (insert a T) - L T
      calc
        L (insert a S) = L S + D S := by simp [D]
        _ =
            Finset.sum S.powerset
                (fun T => pom_axis_decomposability_iff_higher_cross_anomaly L T) +
              Finset.sum S.powerset
                (fun T => pom_axis_decomposability_iff_higher_cross_anomaly D T) := by
                rw [← ih L, ← ih D]
        _ = Finset.sum (insert a S).powerset
            (fun T => pom_axis_decomposability_iff_higher_cross_anomaly L T) := by
              rw [Finset.sum_powerset_insert ha]
              congr 1
              apply Finset.sum_congr rfl
              intro T hT
              have hsub : T ⊆ S := Finset.mem_powerset.mp hT
              have haT : a ∉ T := fun h => ha (hsub h)
              exact (pom_axis_decomposability_iff_higher_cross_anomaly_insert L haT).symm

lemma pom_axis_decomposability_iff_constant_anomaly_zero {k : Nat} (c : ℝ)
    {S : Finset (Fin k)} (hS : S.Nonempty) :
    pom_axis_decomposability_iff_higher_cross_anomaly (fun _ => c) S = 0 := by
  classical
  rcases hS with ⟨a, haS⟩
  rw [← Finset.insert_erase haS]
  rw [pom_axis_decomposability_iff_higher_cross_anomaly_insert (fun _ => c)
    (Finset.notMem_erase a S)]
  simp [pom_axis_decomposability_iff_higher_cross_anomaly]

lemma pom_axis_decomposability_iff_additive_anomaly_zero {k : Nat} (ell : Fin k → ℝ)
    {S : Finset (Fin k)} (hS : 2 ≤ S.card) :
    pom_axis_decomposability_iff_higher_cross_anomaly
      (fun T => Finset.sum T (fun i => ell i)) S = 0 := by
  classical
  obtain ⟨a, haS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have herase_nonempty : (S.erase a).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem haS]
    omega
  rw [← Finset.insert_erase haS]
  rw [pom_axis_decomposability_iff_higher_cross_anomaly_insert
    (fun T : Finset (Fin k) => Finset.sum T (fun i => ell i)) (Finset.notMem_erase a S)]
  have hconst :
      pom_axis_decomposability_iff_higher_cross_anomaly
          (fun T : Finset (Fin k) =>
            Finset.sum (insert a T) (fun i => ell i) - Finset.sum T (fun i => ell i))
          (S.erase a) =
        pom_axis_decomposability_iff_higher_cross_anomaly (fun _ => ell a) (S.erase a) := by
    unfold pom_axis_decomposability_iff_higher_cross_anomaly
    apply Finset.sum_congr rfl
    intro T hT
    have hsub : T ⊆ S.erase a := Finset.mem_powerset.mp hT
    have haT : a ∉ T := fun h => Finset.notMem_erase a S (hsub h)
    simp [Finset.sum_insert haT]
  rw [hconst]
  exact pom_axis_decomposability_iff_constant_anomaly_zero (ell a) herase_nonempty

/-- The requested publication signature is false without an additional normalization such as
`L ∅ = 0`: for `k = 1`, the anomaly condition is vacuous, but axis decomposability still forces
`L ∅ = 0`. This witness justifies the paper-side partial annotation. -/
theorem pom_axis_decomposability_iff_signature_false :
    ¬ ∀ L : Finset (Fin 1) → ℝ,
        ((∃ ell : Fin 1 → ℝ, ∀ S : Finset (Fin 1), L S = Finset.sum S ell) ↔
          (∀ S : Finset (Fin 1), 2 <= S.card →
            pom_axis_decomposability_iff_higher_cross_anomaly L S = 0)) := by
  intro hAll
  let L : Finset (Fin 1) → ℝ := fun S => if S = ∅ then 1 else 0
  have hiff := hAll L
  have hRight : ∀ S : Finset (Fin 1), 2 <= S.card →
      pom_axis_decomposability_iff_higher_cross_anomaly L S = 0 := by
    intro S hS
    have hsubset : S ⊆ ({0} : Finset (Fin 1)) := by
      intro x hx
      fin_cases x
      simp
    have hle : S.card ≤ 1 := by
      simpa using (Finset.card_le_card hsubset : S.card ≤ ({0} : Finset (Fin 1)).card)
    have hFalse : False := by omega
    exact False.elim hFalse
  have hLeft : ∃ ell : Fin 1 → ℝ, ∀ S : Finset (Fin 1), L S = Finset.sum S ell := hiff.mpr hRight
  rcases hLeft with ⟨ell, hell⟩
  have hEmpty : L ∅ = Finset.sum (∅ : Finset (Fin 1)) ell := hell ∅
  simp [L] at hEmpty

/-- Paper label: `thm:pom-axis-decomposability-iff`. With the empty-set normalization restored,
vanishing of all higher Boolean Möbius coefficients is equivalent to additivity on axes. -/
theorem paper_pom_axis_decomposability_iff {k : Nat} (L : Finset (Fin k) → ℝ)
    (h0 : L ∅ = 0) :
    ((∃ ell : Fin k → ℝ, ∀ S : Finset (Fin k), L S = Finset.sum S (fun i => ell i)) ↔
      (∀ S : Finset (Fin k), 2 ≤ S.card →
        pom_axis_decomposability_iff_higher_cross_anomaly L S = 0)) := by
  classical
  constructor
  · rintro ⟨ell, hL⟩ S hS
    simpa [pom_axis_decomposability_iff_higher_cross_anomaly, hL] using
      pom_axis_decomposability_iff_additive_anomaly_zero ell hS
  · intro hcross
    let ell : Fin k → ℝ := fun i => L {i}
    refine ⟨ell, ?_⟩
    intro S
    rw [pom_axis_decomposability_iff_mobius_inversion L S]
    have hterm : ∀ T ∈ S.powerset,
        pom_axis_decomposability_iff_higher_cross_anomaly L T =
          if T.card = 1 then L T else 0 := by
      intro T hT
      by_cases hT0 : T.card = 0
      · have hTempty : T = ∅ := Finset.card_eq_zero.mp hT0
        simp [hTempty, pom_axis_decomposability_iff_higher_cross_anomaly, h0]
      · by_cases hT1 : T.card = 1
        · rcases Finset.card_eq_one.mp hT1 with ⟨i, rfl⟩
          simpa [pom_axis_decomposability_iff_higher_cross_anomaly, h0] using
            (pom_axis_decomposability_iff_higher_cross_anomaly_insert
              (k := k) L (a := i) (S := ∅) (by simp))
        · have hTge : 2 ≤ T.card := by omega
          simp [hT1, hcross T hTge]
    trans Finset.sum S.powerset (fun T => if T.card = 1 then L T else 0)
    · exact Finset.sum_congr rfl hterm
    · rw [← Finset.sum_filter]
      have hfilter :
          S.powerset.filter (fun T : Finset (Fin k) => T.card = 1) = S.powersetCard 1 := by
        ext T
        simp [Finset.mem_powersetCard]
      rw [hfilter, Finset.powersetCard_one]
      simp [ell]

end Omega.POM
