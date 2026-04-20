import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Omega.CircleDimension.ArithmeticSingularRingPrimeFrequencyCharacterEval

namespace Omega.CircleDimension

/-- The finite torus-rotation phase vector extracted from a finite family of character frequencies. -/
def torusRotationPhase {m : ℕ} (α : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun j => t * α j

/-- The observable real-part readout attached to the torus rotation. -/
noncomputable def torusRotationObservable {m : ℕ} (α : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun j => Real.cos (torusRotationPhase α t j)

/-- The observable pair singled out by coordinates `j` and `k`. -/
noncomputable def torusRotationObservablePair {m : ℕ} (α : Fin m → ℝ)
    (j k : Fin m) (t : ℝ) : ℝ × ℝ :=
  (torusRotationObservable α t j, torusRotationObservable α t k)

/-- The full finite-character readout is periodic if some positive time shift fixes every
coordinate. -/
def PeriodicTorusRotationObservable {m : ℕ} (α : Fin m → ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, torusRotationObservable α (t + T) = torusRotationObservable α t

/-- The selected two-coordinate readout is periodic if a single positive time shift fixes both
coordinates simultaneously. -/
def PeriodicTorusRotationObservablePair {m : ℕ} (α : Fin m → ℝ) (j k : Fin m) : Prop :=
  ∃ T : ℝ, 0 < T ∧
    ∀ t : ℝ, torusRotationObservablePair α j k (t + T) = torusRotationObservablePair α j k t

lemma periodic_observable_of_integer_frequencies {m : ℕ} (α : Fin m → ℝ) {base : ℝ}
    (hbase : 0 < base) (z : Fin m → ℤ) (hα : ∀ j, α j = base * z j) :
    PeriodicTorusRotationObservable α := by
  refine ⟨2 * Real.pi / base, by positivity, ?_⟩
  intro t
  funext j
  have hphase :
      torusRotationPhase α (t + 2 * Real.pi / base) j =
        torusRotationPhase α t j + (z j) * (2 * Real.pi) := by
    rw [torusRotationPhase, torusRotationPhase, hα j]
    field_simp [hbase.ne']
  rw [torusRotationObservable, torusRotationObservable, hphase]
  simpa [add_comm, add_left_comm, add_assoc] using
    Real.cos_add_int_mul_two_pi (torusRotationPhase α t j) (z j)

lemma rational_ratio_of_periodic_pair {m : ℕ} {α : Fin m → ℝ} {j k : Fin m}
    (hpair : PeriodicTorusRotationObservablePair α j k) (hk : α k ≠ 0) :
    ¬ Irrational (α j / α k) := by
  rcases hpair with ⟨T, hTpos, hT⟩
  have hT_ne : T ≠ 0 := ne_of_gt hTpos
  have hj0 : Real.cos (T * α j) = 1 := by
    have hzero := congrArg Prod.fst (hT 0)
    simpa [torusRotationObservablePair, torusRotationObservable, torusRotationPhase] using hzero
  have hk0 : Real.cos (T * α k) = 1 := by
    have hzero := congrArg Prod.snd (hT 0)
    simpa [torusRotationObservablePair, torusRotationObservable, torusRotationPhase] using hzero
  rcases (Real.cos_eq_one_iff (T * α j)).mp hj0 with ⟨a, ha⟩
  rcases (Real.cos_eq_one_iff (T * α k)).mp hk0 with ⟨b, hb⟩
  have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hb_ne : b ≠ 0 := by
    intro hb0
    have hzero : T * α k = 0 := by simpa [hb0] using hb.symm
    exact (mul_ne_zero hT_ne hk) hzero
  have hratio : α j / α k = (a : ℝ) / b := by
    have hj : α j = (a : ℝ) * (2 * Real.pi) / T := by
      apply (eq_div_iff hT_ne).2
      nlinarith [ha]
    have hk' : α k = (b : ℝ) * (2 * Real.pi) / T := by
      apply (eq_div_iff hT_ne).2
      nlinarith [hb]
    rw [hj, hk']
    field_simp [hT_ne, htwo_pi_ne, hb_ne]
  intro hirr
  rw [irrational_iff_ne_rational] at hirr
  exact hirr a b hb_ne hratio

/-- The finite-character observable readout coming from the arithmetic singular-ring phase model
is a torus rotation. In the integral-frequency case the readout is periodic; in the irrational
ratio case no common period can exist for the corresponding two-coordinate projection.
    cor:cdim-arithmetic-singular-ring-observable-closure-dichotomy -/
theorem paper_cdim_arithmetic_singular_ring_observable_closure_dichotomy
    {S : Finset ℕ} (omega : S → ℝ) (m : ℕ) (α : Fin m → ℝ) :
    ArithmeticSingularRingPrimeFrequencyCharacterEval S omega ∧
      (∀ base : ℝ, 0 < base → ∀ z : Fin m → ℤ, (∀ j, α j = base * z j) →
        PeriodicTorusRotationObservable α) ∧
      (∀ j k : Fin m, α k ≠ 0 → Irrational (α j / α k) →
        ¬ PeriodicTorusRotationObservablePair α j k) := by
  refine ⟨paper_cdim_arithmetic_singular_ring_prime_frequency_character_eval omega, ?_, ?_⟩
  · intro base hbase z hα
    exact periodic_observable_of_integer_frequencies α hbase z hα
  · intro j k hk hirr hpair
    exact rational_ratio_of_periodic_pair hpair hk hirr

end Omega.CircleDimension
