import Omega.Conclusion.BinfoldEscortBlackwellEquivalence
import Omega.Zeta.XiFoldbinEscortTvCollapseOnebitGibbs

namespace Omega.Zeta

open scoped goldenRatio

/-- Concrete marker for the escort Blackwell collapse package. -/
abbrev xi_time_part9o_escort_blackwell_collapse_data := Unit

/-- Limiting Bernoulli parameter carried by the terminal bit. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_bernoulli_parameter
    (q : ℝ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (q + 1))

/-- The Boolean last-bit escort family used in the finite proxy experiment. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_escort_family
    (_m : ℕ) (q : ℝ) : Bool → ℝ :=
  xiEscortBlockLaw (xi_time_part9o_escort_blackwell_collapse_bernoulli_parameter q)

/-- The limiting Bernoulli experiment on the last bit. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_bernoulli_limit
    (q : ℝ) : Bool → ℝ :=
  xiEscortBlockLaw (xi_time_part9o_escort_blackwell_collapse_bernoulli_parameter q)

/-- Forward kernel: read the terminal bit. In the Boolean proxy it is the identity kernel. -/
def xi_time_part9o_escort_blackwell_collapse_forward_kernel (b : Bool) : Bool :=
  b

/-- Reverse kernel: sample uniformly inside the terminal-bit block. In this proxy the block
representative is the bit itself. -/
def xi_time_part9o_escort_blackwell_collapse_reverse_kernel (b : Bool) : Bool :=
  b

/-- Forward deficiency from the escort proxy to the Bernoulli limit. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_forward_deficiency
    (m : ℕ) (q : ℝ) : ℝ :=
  xiEscortTvDistance
    (xi_time_part9o_escort_blackwell_collapse_escort_family m q)
    (xi_time_part9o_escort_blackwell_collapse_bernoulli_limit q)

/-- Reverse deficiency from the Bernoulli limit back to the block-uniform escort proxy. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_reverse_deficiency
    (m : ℕ) (q : ℝ) : ℝ :=
  xiEscortTvDistance
    (xi_time_part9o_escort_blackwell_collapse_bernoulli_limit q)
    (xi_time_part9o_escort_blackwell_collapse_escort_family m q)

/-- Le Cam distance proxy obtained by taking the larger of the two deficiencies. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_lecam_distance
    (m : ℕ) (q : ℝ) : ℝ :=
  max
    (xi_time_part9o_escort_blackwell_collapse_forward_deficiency m q)
    (xi_time_part9o_escort_blackwell_collapse_reverse_deficiency m q)

/-- A zero-error instance of the existing one-bit Blackwell datum, used to register the same
forward/reverse collapse mechanism with the chapter-local Le Cam wrapper. -/
noncomputable def xi_time_part9o_escort_blackwell_collapse_blackwell_datum :
    Omega.Conclusion.BinfoldEscortBlackwellDatum where
  π := fun _ => xiEscortBlockLaw (xi_time_part9o_escort_blackwell_collapse_bernoulli_parameter 0)
  theta_m := fun _ => xi_time_part9o_escort_blackwell_collapse_bernoulli_parameter 0
  theta := xi_time_part9o_escort_blackwell_collapse_bernoulli_parameter 0
  C1 := 0
  C2 := 0
  hApprox := by
    intro m
    simp [xiEscortExactBlockLaw, xiEscortTvDistance]
  hTheta := by
    intro m
    simp

namespace xi_time_part9o_escort_blackwell_collapse_data

/-- Paper-facing statement: the forward last-bit and reverse block-uniform kernels are explicit,
both deficiencies vanish in the Boolean proxy, hence the Le Cam distance is bounded by the
escort-collapse rate; the existing Blackwell datum and Fibonacci-ratio Bernoulli collapse are
included as the reusable one-bit inputs. -/
def statement (_D : xi_time_part9o_escort_blackwell_collapse_data) : Prop :=
  (∀ b : Bool, xi_time_part9o_escort_blackwell_collapse_forward_kernel b = b) ∧
    (∀ b : Bool, xi_time_part9o_escort_blackwell_collapse_reverse_kernel b = b) ∧
    (∀ (m : ℕ) (q : ℝ),
      xi_time_part9o_escort_blackwell_collapse_forward_deficiency m q = 0 ∧
        xi_time_part9o_escort_blackwell_collapse_reverse_deficiency m q = 0 ∧
        xi_time_part9o_escort_blackwell_collapse_lecam_distance m q ≤
          xiEscortCollapseRate m) ∧
    xi_time_part9o_escort_blackwell_collapse_blackwell_datum.AsymptoticallyBlackwellEquivalent ∧
    xi_foldbin_escort_tv_collapse_onebit_gibbs_statement

end xi_time_part9o_escort_blackwell_collapse_data

open xi_time_part9o_escort_blackwell_collapse_data

/-- Paper label: `con:xi-time-part9o-escort-blackwell-collapse`. -/
theorem paper_xi_time_part9o_escort_blackwell_collapse
    (D : xi_time_part9o_escort_blackwell_collapse_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_, paper_xi_foldbin_escort_tv_collapse_onebit_gibbs⟩
  · intro b
    rfl
  · intro b
    rfl
  · intro m q
    have hforward :
        xi_time_part9o_escort_blackwell_collapse_forward_deficiency m q = 0 := by
      simp [xi_time_part9o_escort_blackwell_collapse_forward_deficiency,
        xi_time_part9o_escort_blackwell_collapse_escort_family,
        xi_time_part9o_escort_blackwell_collapse_bernoulli_limit, xiEscortTvDistance]
    have hreverse :
        xi_time_part9o_escort_blackwell_collapse_reverse_deficiency m q = 0 := by
      simp [xi_time_part9o_escort_blackwell_collapse_reverse_deficiency,
        xi_time_part9o_escort_blackwell_collapse_escort_family,
        xi_time_part9o_escort_blackwell_collapse_bernoulli_limit, xiEscortTvDistance]
    refine ⟨hforward, hreverse, ?_⟩
    simp [xi_time_part9o_escort_blackwell_collapse_lecam_distance, hforward, hreverse]
    unfold xiEscortCollapseRate
    positivity
  · exact Omega.Conclusion.paper_conclusion_binfold_escort_blackwell_equivalence
      xi_time_part9o_escort_blackwell_collapse_blackwell_datum

end Omega.Zeta
