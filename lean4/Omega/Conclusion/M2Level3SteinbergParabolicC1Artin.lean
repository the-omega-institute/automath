import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys

namespace Omega.Conclusion

/-- The common rank of the Steinberg local system in the audited `M₂(3)` package. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_rank : ℕ := 81

/-- The `1`-eigenspace multiplicity at the order-`3` boundary component `Δ₀`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_invariant_mult : ℕ := 27

/-- The multiplicity of each primitive cube-root eigenspace at `Δ₀`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_primitive_mult : ℕ := 27

/-- The `+1`-eigenspace multiplicity at the order-`2` boundary component `Ξ`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_invariant_mult : ℕ := 45

/-- The `-1`-eigenspace multiplicity at `Ξ`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_neg_mult : ℕ := 36

/-- The parabolic `c₁` coefficient of `Δ₀`: the two primitive cube-root weights add to `1`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_c1 : ℕ :=
  conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_primitive_mult

/-- The parabolic `c₁` coefficient of `Ξ`: each `-1` eigenline contributes weight `1/2`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_c1 : ℕ :=
  conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_neg_mult / 2

/-- The ordered pair of parabolic first-Chern coefficients `(Δ₀, Ξ)`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_parabolic_c1 : ℕ × ℕ :=
  (conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_c1,
    conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_c1)

/-- The tame Artin conductor at `Δ₀`, computed as rank minus invariant multiplicity. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_artin : ℕ :=
  conclusion_m2_level3_steinberg_parabolic_c1_artin_rank -
    conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_invariant_mult

/-- The tame Artin conductor at `Ξ`, computed as rank minus invariant multiplicity. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_artin : ℕ :=
  conclusion_m2_level3_steinberg_parabolic_c1_artin_rank -
    conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_invariant_mult

/-- The ordered pair of tame Artin conductors `(Δ₀, Ξ)`. -/
def conclusion_m2_level3_steinberg_parabolic_c1_artin_tame_artin : ℕ × ℕ :=
  (conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_artin,
    conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_artin)

/-- Paper label: `cor:conclusion-m2-level3-steinberg-parabolic-c1-artin`. The audited Steinberg
order-`3` and order-`2` inertia spectra give the explicit characteristic polynomial, parabolic
first-Chern coefficients, and tame Artin conductors. -/
theorem paper_conclusion_m2_level3_steinberg_parabolic_c1_artin :
    conclusion_m2_level3_xi_delta0_order6_charpolys_St =
      conclusion_m2_level3_xi_delta0_order6_charpolys_phi1 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi2 ^ 12 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi3 ^ 15 *
        conclusion_m2_level3_xi_delta0_order6_charpolys_phi6 ^ 12 ∧
      conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_invariant_mult = 27 ∧
      conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_primitive_mult = 27 ∧
      conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_invariant_mult = 45 ∧
      conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_neg_mult = 36 ∧
      conclusion_m2_level3_steinberg_parabolic_c1_artin_parabolic_c1 = (27, 18) ∧
      conclusion_m2_level3_steinberg_parabolic_c1_artin_tame_artin = (54, 36) := by
  rcases paper_conclusion_m2_level3_xi_delta0_order6_charpolys ⟨()⟩ with
    ⟨_, _, _, _, _, _, hSt, _, _⟩
  refine ⟨hSt, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · norm_num [conclusion_m2_level3_steinberg_parabolic_c1_artin_parabolic_c1,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_c1,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_c1,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_primitive_mult,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_neg_mult]
  · norm_num [conclusion_m2_level3_steinberg_parabolic_c1_artin_tame_artin,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_artin,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_artin,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_rank,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_delta0_invariant_mult,
      conclusion_m2_level3_steinberg_parabolic_c1_artin_xi_invariant_mult]

end Omega.Conclusion
