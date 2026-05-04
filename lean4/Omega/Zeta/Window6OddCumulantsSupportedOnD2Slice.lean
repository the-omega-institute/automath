import Mathlib.Tactic
import Omega.Zeta.XiTimePart9xabWindow6FourpointFiberRanktwoBernoulliFactorization
import Omega.Conclusion.Window6D2SliceUniqueLocalInteractionLayer

namespace Omega.Zeta

/-- The three local window-6 hidden layers, represented as dimensions `2`, `3`, and `4`. -/
abbrev xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer := Fin 3

/-- The product layer `d = 2`. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer2 :
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer :=
  ⟨0, by decide⟩

/-- The `D₂ = A₁ × A₁` interaction slice, indexed by the three-point layer `d = 3`. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3 :
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer :=
  ⟨1, by decide⟩

/-- The product layer `d = 4`. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer4 :
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer :=
  ⟨2, by decide⟩

/-- Centered hidden offsets for the three local laws. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets
    (d : xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer) : Finset ℚ :=
  match d.val with
  | 0 => ({(-17 : ℚ), 17} : Finset ℚ)
  | 1 => ({(-55 / 3 : ℚ), 8 / 3, 47 / 3} : Finset ℚ)
  | _ => ({(-55 / 2 : ℚ), -13 / 2, 13 / 2, 55 / 2} : Finset ℚ)

/-- Cardinal denominator of the uniform local law. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality
    (d : xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer) : ℚ :=
  match d.val with
  | 0 => 2
  | 1 => 3
  | _ => 4

/-- Centered local moment of order `k`. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment
    (d : xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer) (k : ℕ) : ℚ :=
  (∑ z ∈ xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets d,
      z ^ k) /
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality d

/-- For centered variables, the second cumulant is the second centered moment. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant2
    (d : xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer) : ℚ :=
  xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment d 2

/-- For centered variables, the third cumulant is the third centered moment. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3
    (d : xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer) : ℚ :=
  xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment d 3

/-- Additive third cumulant of an independently weighted finite product of local laws. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_globalCumulant3
    {n : ℕ}
    (d : Fin n → xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer)
    (a : Fin n → ℚ) : ℚ :=
  ∑ x : Fin n,
    a x ^ 3 *
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3 (d x)

/-- Concrete local arithmetic and finite-product additivity statement for the window-6 odd
cumulants. -/
def xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_statement : Prop :=
  xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer2 2 = 289 ∧
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3 2 = 1766 / 9 ∧
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer4 2 = 1597 / 4 ∧
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer2 = 0 ∧
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3 = -20680 / 27 ∧
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer4 = 0 ∧
    (∀ {n : ℕ}
      (d : Fin n → xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer)
      (a : Fin n → ℚ),
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_globalCumulant3 d a =
          (-20680 / 27 : ℚ) *
            ∑ x ∈ Finset.univ.filter
              (fun x : Fin n =>
                d x =
                  xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3),
              a x ^ 3)

/-- Paper label: `thm:xi-time-part9xaba-window6-odd-cumulants-supported-on-d2-slice`. -/
theorem paper_xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice :
    xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer2]
  · norm_num [xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3]
  · norm_num [xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer4]
  · norm_num [xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer2]
  · norm_num [xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3]
  · norm_num [xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
      xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer4]
  · intro n d a
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rcases hdx : d x with ⟨k, hk⟩
    interval_cases k <;>
      norm_num [hdx,
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_globalCumulant3,
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cumulant3,
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_localMoment,
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_centeredOffsets,
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_cardinality,
        xi_time_part9xaba_window6_odd_cumulants_supported_on_d2_slice_layer3];
      ring

end Omega.Zeta
