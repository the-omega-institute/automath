import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open scoped BigOperators Topology

namespace Omega.Zeta

noncomputable section

/-- The canonical finite-atom support `1, 2, ..., n + 1` used as a concrete zero-dispersion law. -/
def zeroDispersionAtom {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  (i : ℝ) + 1

/-- The finite-atom profile `Φ(t) = E[min(1, t / Z)]` on the canonical support. -/
def zeroDispersionPhi {n : ℕ} (p : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), p i * min 1 (t / zeroDispersionAtom i)

/-- The logarithmic profile `Ψ(c) = Φ(exp c)`. -/
def zeroDispersionPsi {n : ℕ} (p : Fin (n + 1) → ℝ) (c : ℝ) : ℝ :=
  zeroDispersionPhi p (Real.exp c)

/-- The tail-slope profile `q(t) = E[Z⁻¹ 1_{Z > t}]` for the canonical finite-atom law. -/
def zeroDispersionQ {n : ℕ} (p : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), if t < zeroDispersionAtom i then p i / zeroDispersionAtom i else 0

/-- Regularity package for the concrete finite-atom profile `Φ`. -/
def zeroDispersionPhiRegularity {n : ℕ} (p : Fin (n + 1) → ℝ) : Prop :=
  Continuous (zeroDispersionPhi p) ∧
    Monotone (zeroDispersionPhi p) ∧
    ∀ t, 0 ≤ t → 0 ≤ zeroDispersionPhi p t ∧ zeroDispersionPhi p t ≤ 1

/-- In the finite-atom model, the derivative information is encoded by the exact jump formula for
`q` across the integer thresholds supporting the law. -/
def zeroDispersionPhiDerivativeEqQ {n : ℕ} (p : Fin (n + 1) → ℝ) : Prop :=
  ∀ i : Fin (n + 1),
    zeroDispersionQ p (i : ℝ) - zeroDispersionQ p ((i : ℝ) + 1) = p i / zeroDispersionAtom i

/-- Knowing the `q`-profile, hence the full `Ψ`-curve, uniquely determines the atom weights on the
fixed support `1, 2, ..., n + 1`. -/
def zeroDispersionLawRecoverableFromPsi {n : ℕ} (p : Fin (n + 1) → ℝ) : Prop :=
  ∀ p' : Fin (n + 1) → ℝ, (∀ t, zeroDispersionQ p' t = zeroDispersionQ p t) → p' = p

private lemma zeroDispersionAtom_pos {n : ℕ} (i : Fin (n + 1)) : 0 < zeroDispersionAtom i := by
  unfold zeroDispersionAtom
  positivity

private lemma zeroDispersionAtom_ne_zero {n : ℕ} (i : Fin (n + 1)) :
    zeroDispersionAtom i ≠ 0 :=
  ne_of_gt (zeroDispersionAtom_pos i)

private lemma zeroDispersionQ_gap {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    zeroDispersionQ p (i : ℝ) - zeroDispersionQ p ((i : ℝ) + 1) = p i / zeroDispersionAtom i := by
  unfold zeroDispersionQ
  have hrewrite :
      (∑ j : Fin (n + 1), if (i : ℝ) < zeroDispersionAtom j then p j / zeroDispersionAtom j else 0) -
          (∑ j : Fin (n + 1),
            if (i : ℝ) + 1 < zeroDispersionAtom j then p j / zeroDispersionAtom j else 0) =
        ∑ j : Fin (n + 1),
          ((if (i : ℝ) < zeroDispersionAtom j then p j / zeroDispersionAtom j else 0) -
            (if (i : ℝ) + 1 < zeroDispersionAtom j then p j / zeroDispersionAtom j else 0)) := by
    rw [← Finset.sum_sub_distrib]
  rw [hrewrite]
  let f : Fin (n + 1) → ℝ := fun j =>
    ((if (i : ℝ) < zeroDispersionAtom j then p j / zeroDispersionAtom j else 0) -
      (if (i : ℝ) + 1 < zeroDispersionAtom j then p j / zeroDispersionAtom j else 0))
  change ∑ j : Fin (n + 1), f j = p i / zeroDispersionAtom i
  rw [Finset.sum_eq_single i]
  · simp [f, zeroDispersionAtom]
  · intro j _ hj
    dsimp [f]
    by_cases hji : j.1 < i.1
    · have hfalse₁ : ¬ (i : ℝ) < zeroDispersionAtom j := by
        have hnat : j.1 + 1 ≤ i.1 := Nat.succ_le_of_lt hji
        have hreal : zeroDispersionAtom j ≤ (i : ℝ) := by
          simpa [zeroDispersionAtom] using (show ((j : ℝ) + 1) ≤ (i : ℝ) by exact_mod_cast hnat)
        exact not_lt.mpr hreal
      have hfalse₂ : ¬ (i : ℝ) + 1 < zeroDispersionAtom j := by
        have hnat : j.1 + 1 ≤ i.1 + 1 := Nat.succ_le_succ (Nat.le_of_lt hji)
        have hreal : zeroDispersionAtom j ≤ (i : ℝ) + 1 := by
          simpa [zeroDispersionAtom] using
            (show ((j : ℝ) + 1) ≤ (i : ℝ) + 1 by exact_mod_cast hnat)
        exact not_lt.mpr hreal
      simp [hfalse₁, hfalse₂]
    · have hij_ne : i.1 ≠ j.1 := by
        intro hij
        apply hj
        exact Fin.ext hij.symm
      have hij : i.1 < j.1 := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hji) hij_ne
      have htrue₁ : (i : ℝ) < zeroDispersionAtom j := by
        have hnat : i.1 < j.1 + 1 := lt_trans hij (Nat.lt_succ_self _)
        simpa [zeroDispersionAtom] using (show (i : ℝ) < (j : ℝ) + 1 by exact_mod_cast hnat)
      have htrue₂ : (i : ℝ) + 1 < zeroDispersionAtom j := by
        have hnat : i.1 + 1 < j.1 + 1 := Nat.succ_lt_succ hij
        simpa [zeroDispersionAtom] using
          (show (i : ℝ) + 1 < (j : ℝ) + 1 by exact_mod_cast hnat)
      simp [htrue₁, htrue₂]
  · simp [f]

private lemma recover_zeroDispersion_weight_from_q {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    p i = zeroDispersionAtom i *
      (zeroDispersionQ p (i : ℝ) - zeroDispersionQ p ((i : ℝ) + 1)) := by
  calc
    p i = zeroDispersionAtom i * (p i / zeroDispersionAtom i) := by
      field_simp [zeroDispersionAtom_ne_zero i]
    _ = zeroDispersionAtom i *
        (zeroDispersionQ p (i : ℝ) - zeroDispersionQ p ((i : ℝ) + 1)) := by
      rw [zeroDispersionQ_gap]

private lemma zeroDispersionLawRecoverable {n : ℕ} (p p' : Fin (n + 1) → ℝ)
    (hq : ∀ t, zeroDispersionQ p' t = zeroDispersionQ p t) :
    p' = p := by
  funext i
  calc
    p' i = zeroDispersionAtom i *
        (zeroDispersionQ p' (i : ℝ) - zeroDispersionQ p' ((i : ℝ) + 1)) :=
      recover_zeroDispersion_weight_from_q p' i
    _ = zeroDispersionAtom i *
        (zeroDispersionQ p (i : ℝ) - zeroDispersionQ p ((i : ℝ) + 1)) := by
      rw [hq, hq]
    _ = p i := by
      rw [recover_zeroDispersion_weight_from_q p i]

/-- Paper label: `thm:xi-zero-dispersion-identifiability`.
For the concrete finite-atom law supported on `1, 2, ..., n + 1`, the profile `Φ(t)` is regular,
the tail-slope profile `q(t)` has the exact jump formula that recovers each atom weight, and the
full `q`-profile therefore determines the law behind `Ψ(c) = Φ(exp c)`. -/
theorem paper_xi_zero_dispersion_identifiability {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin (n + 1), p i = 1) :
    zeroDispersionPhiRegularity p ∧
      zeroDispersionPhiDerivativeEqQ p ∧
      zeroDispersionLawRecoverableFromPsi p := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · unfold zeroDispersionPhi
      fun_prop
    · intro s t hst
      unfold zeroDispersionPhi
      refine Finset.sum_le_sum ?_
      intro i hi
      have hdiv : s / zeroDispersionAtom i ≤ t / zeroDispersionAtom i := by
        exact div_le_div_of_nonneg_right hst (le_of_lt (zeroDispersionAtom_pos i))
      exact mul_le_mul_of_nonneg_left (min_le_min_left 1 hdiv) (hp_nonneg i)
    · intro t ht
      constructor
      · unfold zeroDispersionPhi
        exact Finset.sum_nonneg fun i _ =>
          mul_nonneg (hp_nonneg i)
            (le_min zero_le_one (div_nonneg ht (le_of_lt (zeroDispersionAtom_pos i))))
      · unfold zeroDispersionPhi
        calc
          ∑ i : Fin (n + 1), p i * min 1 (t / zeroDispersionAtom i)
              ≤ ∑ i : Fin (n + 1), p i := by
                refine Finset.sum_le_sum ?_
                intro i hi
                exact mul_le_of_le_one_right (hp_nonneg i) (min_le_left _ _)
          _ = 1 := hp_sum
  · intro i
    exact zeroDispersionQ_gap p i
  · intro p' hq
    exact zeroDispersionLawRecoverable p p' hq

end

end Omega.Zeta
