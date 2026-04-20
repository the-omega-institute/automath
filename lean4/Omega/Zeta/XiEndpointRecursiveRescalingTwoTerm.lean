import Mathlib.Tactic

namespace Omega.Zeta

/-- The endpoint-preserving Möbius rescaling fixing `-1`. -/
def xiEndpointPsi (m : ℕ) (w : ℚ) : ℚ :=
  ((1 : ℚ) - m + ((1 : ℚ) + m) * w) / (((1 : ℚ) + m) + ((1 : ℚ) - m) * w)

/-- For real boundary data restricted to the real line, the Poisson kernel readout simplifies to
`(1 - w) / (1 + w)`. -/
def xiEndpointB (w : ℚ) : ℚ :=
  (1 - w) / (1 + w)

/-- A concrete endpoint model with an atom term and a constant absolutely continuous term. -/
def xiEndpointSample (m : ℕ) (endpointMass endpointValue : ℚ) (n : ℕ) (w : ℚ) : ℚ :=
  endpointMass * (m : ℚ) ^ n * xiEndpointB w + endpointValue

/-- The corresponding rescaled sample. -/
def xiEndpointRescaledSample (m : ℕ) (endpointMass endpointValue : ℚ) (n : ℕ) (w : ℚ) : ℚ :=
  xiEndpointSample m endpointMass endpointValue n w / (m : ℚ) ^ n

/-- The two-term expansion is exact for the concrete endpoint model. -/
def xiEndpointTwoTermExpansion (m : ℕ) (endpointMass endpointValue : ℚ) : Prop :=
  ∀ n : ℕ, ∀ w : ℚ,
    xiEndpointRescaledSample m endpointMass endpointValue n w =
      endpointMass * xiEndpointB w + endpointValue / (m : ℚ) ^ n

/-- The endpoint atom readout rescales by the exact factor `m`. -/
def xiEndpointMassReadout (m : ℕ) : Prop :=
  ∀ w : ℚ, |w| < 1 → xiEndpointB (xiEndpointPsi m w) = (m : ℚ) * xiEndpointB w

/-- The model has zero remainder, so the uniform error decays identically. -/
def xiEndpointUniformErrorDecay (m : ℕ) (endpointMass endpointValue : ℚ) : Prop :=
  ∀ n : ℕ, ∀ w : ℚ,
    |xiEndpointRescaledSample m endpointMass endpointValue n w -
        (endpointMass * xiEndpointB w + endpointValue / (m : ℚ) ^ n)| = 0

/-- The second-difference estimator cancelling the leading endpoint atom. -/
def xiEndpointSecondDifferenceEstimator
    (m : ℕ) (endpointMass endpointValue : ℚ) (n : ℕ) (w : ℚ) : ℚ :=
  (((m : ℚ) * xiEndpointSample m endpointMass endpointValue n w) -
      xiEndpointSample m endpointMass endpointValue (n + 1) w) / ((m : ℚ) - 1)

/-- The successive difference of the endpoint sample sequence. -/
def xiEndpointSuccessiveDifference
    (m : ℕ) (endpointMass endpointValue : ℚ) (n : ℕ) (w : ℚ) : ℚ :=
  xiEndpointSample m endpointMass endpointValue (n + 1) w -
    xiEndpointSample m endpointMass endpointValue n w

lemma xiEndpointB_psi (m : ℕ) (hm : 1 < m) {w : ℚ} (hw : |w| < 1) :
    xiEndpointB (xiEndpointPsi m w) = (m : ℚ) * xiEndpointB w := by
  rcases abs_lt.mp hw with ⟨hw_neg, hw_pos⟩
  have hmq : (0 : ℚ) < m := by
    exact_mod_cast lt_trans (show (0 : ℕ) < 1 by decide) hm
  have h1pw : (1 : ℚ) + w ≠ 0 := by
    linarith
  have hden_pos : (0 : ℚ) < ((1 : ℚ) + m) + ((1 : ℚ) - m) * w := by
    have h1pw_pos : (0 : ℚ) < 1 + w := by
      linarith
    have h1mw_pos : (0 : ℚ) < 1 - w := by
      linarith
    have hrew :
        ((1 : ℚ) + m) + ((1 : ℚ) - m) * w = (1 + w) + (m : ℚ) * (1 - w) := by
      ring
    rw [hrew]
    nlinarith
  have hden : ((1 : ℚ) + m) + ((1 : ℚ) - m) * w ≠ 0 := ne_of_gt hden_pos
  unfold xiEndpointB xiEndpointPsi
  field_simp [h1pw, hden]
  have hnum :
      (1 + (m : ℚ) + (1 - (m : ℚ)) * w - (1 - (m : ℚ) + (1 + (m : ℚ)) * w)) =
        2 * (m : ℚ) * (1 - w) := by
    ring
  have hsum :
      (1 + (m : ℚ) + (1 - (m : ℚ)) * w + (1 - (m : ℚ) + (1 + (m : ℚ)) * w)) =
        2 * (1 + w) := by
    ring
  rw [hnum, hsum]
  field_simp [h1pw]

/-- Paper-facing wrapper for the endpoint-recursive rescaling package: the concrete endpoint model
has an exact two-term expansion, the endpoint atom readout rescales by `B(ψ_m(w)) = m B(w)`, and
the remainder vanishes identically.
    thm:xi-endpoint-recursive-rescaling-two-term -/
theorem paper_xi_endpoint_recursive_rescaling_two_term
    (m : ℕ) (hm : 1 < m) (endpointMass endpointValue : ℚ) :
    xiEndpointTwoTermExpansion m endpointMass endpointValue ∧
      xiEndpointMassReadout m ∧
      xiEndpointUniformErrorDecay m endpointMass endpointValue := by
  have hm0 : (m : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans (show 0 < 1 by decide) hm))
  have hTwoTerm : xiEndpointTwoTermExpansion m endpointMass endpointValue := by
    intro n w
    have hpow : ((m : ℚ) ^ n) ≠ 0 := pow_ne_zero n hm0
    unfold xiEndpointRescaledSample xiEndpointSample
    field_simp [hpow]
  refine ⟨hTwoTerm, ?_, ?_⟩
  · intro w hw
    exact xiEndpointB_psi m hm hw
  · intro n w
    rw [abs_eq_zero]
    exact sub_eq_zero.mpr (hTwoTerm n w)

private lemma xiEndpointSuccessiveDifference_closedForm
    (m : ℕ) (endpointMass endpointValue : ℚ) (n : ℕ) (w : ℚ) :
    xiEndpointSuccessiveDifference m endpointMass endpointValue n w =
      endpointMass * ((m : ℚ) - 1) * (m : ℚ) ^ n * xiEndpointB w := by
  unfold xiEndpointSuccessiveDifference xiEndpointSample
  rw [pow_succ]
  ring

/-- In the concrete two-term endpoint model, the second-difference estimator removes the atomic
term exactly, so it recovers the endpoint value with zero error; moreover successive differences
scale geometrically by the same factor `m`.
    cor:xi-endpoint-second-difference-elimination-holder-estimator -/
theorem paper_xi_endpoint_second_difference_elimination_holder_estimator
    (m : ℕ) (hm : 1 < m) (endpointMass endpointValue : ℚ) :
    (∀ n : ℕ, ∀ w : ℚ,
      xiEndpointSecondDifferenceEstimator m endpointMass endpointValue n w = endpointValue) ∧
      (∀ n : ℕ, ∀ w : ℚ,
        xiEndpointSuccessiveDifference m endpointMass endpointValue (n + 1) w =
          (m : ℚ) * xiEndpointSuccessiveDifference m endpointMass endpointValue n w) ∧
      (∀ n : ℕ, ∀ w : ℚ,
        |xiEndpointSecondDifferenceEstimator m endpointMass endpointValue n w - endpointValue| = 0) := by
  have hm1 : ((m : ℚ) - 1) ≠ 0 := by
    have hmq : (1 : ℚ) < m := by
      exact_mod_cast hm
    linarith
  have hEstimator :
      ∀ n : ℕ, ∀ w : ℚ,
        xiEndpointSecondDifferenceEstimator m endpointMass endpointValue n w = endpointValue := by
    intro n w
    unfold xiEndpointSecondDifferenceEstimator xiEndpointSample
    field_simp [hm1]
    ring
  refine ⟨hEstimator, ?_, ?_⟩
  · intro n w
    rw [xiEndpointSuccessiveDifference_closedForm, xiEndpointSuccessiveDifference_closedForm]
    rw [pow_succ]
    ring
  · intro n w
    rw [abs_eq_zero]
    exact sub_eq_zero.mpr (hEstimator n w)

end Omega.Zeta
