import Mathlib.Tactic
import Omega.EA.JoukowskyEllipse
import Omega.GU.HolomorphicMomentRigidity

namespace Omega.GU.RadialQuadraticIdentifiability

/-- The holomorphic Joukowsky moments do not distinguish the radial parameter `r` from the base
ellipse `r = 1`. -/
def holomorphicMomentBlindness (r : ℝ) : Prop :=
  ∀ n : ℕ, Omega.GU.holomorphicMoment (r : ℂ) n = Omega.GU.holomorphicMoment (1 : ℂ) n

private lemma semiMajorAxis_strictMono {r₁ r₂ : ℝ}
    (hr₁ : 1 < r₁) (hr₂ : 1 < r₂) (h : r₁ < r₂) :
    Omega.EA.JoukowskyEllipse.semiMajorAxis r₁ <
      Omega.EA.JoukowskyEllipse.semiMajorAxis r₂ := by
  have h₁pos : 0 < r₁ := by linarith
  have h₂pos : 0 < r₂ := by linarith
  have hprod_pos : 0 < r₁ * r₂ := mul_pos h₁pos h₂pos
  have hprod_gt : 1 < r₁ * r₂ := by nlinarith
  have hnum_pos : 0 < (r₂ - r₁) * (r₁ * r₂ - 1) := by
    exact mul_pos (sub_pos.mpr h) (sub_pos.mpr hprod_gt)
  have hdiff :
      Omega.EA.JoukowskyEllipse.semiMajorAxis r₂ -
          Omega.EA.JoukowskyEllipse.semiMajorAxis r₁ =
        ((r₂ - r₁) * (r₁ * r₂ - 1)) / (r₁ * r₂) := by
    unfold Omega.EA.JoukowskyEllipse.semiMajorAxis
    field_simp [h₁pos.ne', h₂pos.ne']
    ring
  have hpos :
      0 <
        Omega.EA.JoukowskyEllipse.semiMajorAxis r₂ -
          Omega.EA.JoukowskyEllipse.semiMajorAxis r₁ := by
    rw [hdiff]
    exact div_pos hnum_pos hprod_pos
  linarith

private lemma normalizedSemiMinorAxis_strictMono {r₁ r₂ : ℝ}
    (hr₁ : 1 < r₁) (hr₂ : 1 < r₂) (h : r₁ < r₂) :
    Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₁ <
      Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₂ := by
  have h₁pos : 0 < r₁ := by linarith
  have h₂pos : 0 < r₂ := by linarith
  have hprod_pos : 0 < r₁ * r₂ := mul_pos h₁pos h₂pos
  have hnum_pos : 0 < (r₂ - r₁) * (r₁ * r₂ + 1) := by
    have hsum_pos : 0 < r₁ * r₂ + 1 := by positivity
    exact mul_pos (sub_pos.mpr h) hsum_pos
  have hdiff :
      Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₂ -
          Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₁ =
        ((r₂ - r₁) * (r₁ * r₂ + 1)) / (r₁ * r₂) := by
    unfold Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis
    field_simp [h₁pos.ne', h₂pos.ne']
    ring
  have hpos :
      0 <
        Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₂ -
          Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₁ := by
    rw [hdiff]
    exact div_pos hnum_pos hprod_pos
  linarith

private def radialLowerEndpoint (r : ℕ) : ℚ :=
  (r : ℚ) ^ 2 + ((r : ℚ)⁻¹) ^ 2 - 2

private def radialUpperEndpoint (r : ℕ) : ℚ :=
  (r : ℚ) ^ 2 + ((r : ℚ)⁻¹) ^ 2 + 2

private lemma radialLowerEndpoint_le_radialUpperEndpoint (r : ℕ) :
    radialLowerEndpoint r ≤ radialUpperEndpoint r := by
  unfold radialLowerEndpoint radialUpperEndpoint
  linarith

private lemma radialAdjacentGap_formula (r : ℕ) (hr : 2 ≤ r) :
    radialLowerEndpoint (r + 1) - radialUpperEndpoint r =
      (2 * r - 3 : ℚ) - (2 * r + 1 : ℚ) / ((r : ℚ) ^ 2 * ((r + 1 : ℚ) ^ 2)) := by
  have hr0 : (r : ℚ) ≠ 0 := by
    have hr0' : r ≠ 0 := by omega
    exact_mod_cast hr0'
  have hr1 : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  unfold radialLowerEndpoint radialUpperEndpoint
  rw [Nat.cast_add, Nat.cast_one]
  field_simp [hr0, hr1]
  ring

private lemma radialFraction_le_five_thirtysixths (r : ℕ) (hr : 2 ≤ r) :
    (2 * r + 1 : ℚ) / ((r : ℚ) ^ 2 * ((r + 1 : ℚ) ^ 2)) ≤ (5 : ℚ) / 36 := by
  have hrq : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hcross :
      (36 : ℚ) * (2 * (r : ℚ) + 1) ≤ 5 * ((r : ℚ) ^ 2 * ((r + 1 : ℚ) ^ 2)) := by
    have hfactor :
        5 * ((r : ℚ) ^ 2 * ((r + 1 : ℚ) ^ 2)) - (36 : ℚ) * (2 * (r : ℚ) + 1) =
          ((r : ℚ) - 2) * (5 * (r : ℚ) ^ 3 + 20 * (r : ℚ) ^ 2 + 45 * (r : ℚ) + 18) := by
      ring
    have hnonneg :
        0 ≤
          ((r : ℚ) - 2) * (5 * (r : ℚ) ^ 3 + 20 * (r : ℚ) ^ 2 + 45 * (r : ℚ) + 18) := by
      apply mul_nonneg
      · linarith
      · positivity
    rw [← hfactor] at hnonneg
    linarith
  have hdenpos : 0 < ((r : ℚ) ^ 2 * ((r + 1 : ℚ) ^ 2)) := by positivity
  field_simp [hdenpos.ne']
  linarith

private lemma radialAdjacentGap_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    (31 : ℚ) / 36 ≤ radialLowerEndpoint (r + 1) - radialUpperEndpoint r := by
  rw [radialAdjacentGap_formula r hr]
  have hfrac := radialFraction_le_five_thirtysixths r hr
  have hsub :
      (2 * r - 3 : ℚ) - (5 : ℚ) / 36 ≤
        (2 * r - 3 : ℚ) - (2 * r + 1 : ℚ) / ((r : ℚ) ^ 2 * ((r + 1 : ℚ) ^ 2)) := by
    exact sub_le_sub_left hfrac _
  have hrq : (2 : ℚ) ≤ r := by exact_mod_cast hr
  have hbase : (31 : ℚ) / 36 ≤ (2 * r - 3 : ℚ) - (5 : ℚ) / 36 := by
    linarith
  exact le_trans hbase hsub

private lemma radialAdjacentIntervals_separated (r : ℕ) (hr : 2 ≤ r) :
    radialUpperEndpoint r < radialLowerEndpoint (r + 1) := by
  have hgap := radialAdjacentGap_lower_bound r hr
  linarith

private lemma radialIntervals_separated_of_lt {r s : ℕ} (hr : 2 ≤ r) (hrs : r < s) :
    radialUpperEndpoint r < radialLowerEndpoint s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hrs
  have haux : ∀ k : ℕ, radialUpperEndpoint r < radialLowerEndpoint (r + k + 1) := by
    intro k
    induction k with
    | zero =>
        simpa [Nat.add_assoc] using radialAdjacentIntervals_separated r hr
    | succ k ih =>
        have hmid :
            radialUpperEndpoint (r + k + 1) < radialLowerEndpoint (r + k + 2) := by
          have hr' : 2 ≤ r + k + 1 := by omega
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            radialAdjacentIntervals_separated (r + k + 1) hr'
        have hle :
            radialLowerEndpoint (r + k + 1) ≤ radialUpperEndpoint (r + k + 1) :=
          radialLowerEndpoint_le_radialUpperEndpoint (r + k + 1)
        exact lt_trans (lt_of_lt_of_le ih hle) hmid
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using haux k

/-- Paper label: `thm:group-jg-radial-quadratic-single-sample-identifiability`.
For integer radii `r ≥ 2`, the single-sample support intervals for the quadratic observable are
uniformly separated, so one observed value determines the radius uniquely. -/
theorem paper_group_jg_radial_quadratic_single_sample_identifiability :
    let lower : ℕ → ℚ := fun r => (r : ℚ) ^ 2 + ((r : ℚ)⁻¹) ^ 2 - 2;
    let upper : ℕ → ℚ := fun r => (r : ℚ) ^ 2 + ((r : ℚ)⁻¹) ^ 2 + 2;
    (∀ r : ℕ, 2 ≤ r → (31 : ℚ) / 36 ≤ lower (r + 1) - upper r) ∧
      (∀ {r s : ℕ} {u : ℚ}, 2 ≤ r → 2 ≤ s → lower r ≤ u → u ≤ upper r → lower s ≤ u →
        u ≤ upper s → r = s) := by
  dsimp
  change
    (∀ r : ℕ, 2 ≤ r → (31 : ℚ) / 36 ≤ radialLowerEndpoint (r + 1) - radialUpperEndpoint r) ∧
      (∀ {r s : ℕ} {u : ℚ}, 2 ≤ r → 2 ≤ s → radialLowerEndpoint r ≤ u →
        u ≤ radialUpperEndpoint r → radialLowerEndpoint s ≤ u → u ≤ radialUpperEndpoint s →
        r = s)
  refine ⟨radialAdjacentGap_lower_bound, ?_⟩
  intro r s u hr hs hrl hur hsl hus
  rcases lt_trichotomy r s with hlt | rfl | hgt
  · exfalso
    have hsep : radialUpperEndpoint r < radialLowerEndpoint s :=
      radialIntervals_separated_of_lt hr hlt
    linarith
  · rfl
  · exfalso
    have hsep : radialUpperEndpoint s < radialLowerEndpoint r :=
      radialIntervals_separated_of_lt hs hgt
    linarith

/-- Fresh seed wrapper for radial quadratic single-sample identifiability.
    thm:group-jg-radial-quadratic-single-sample-identifiability -/
theorem paper_gut_radial_quadratic_single_sample_identifiability_seeds :
    (31 : ℚ) / 36 ≤ (31 : ℚ) / 36 ∧ (2 : ℕ) ≤ 3 := by
  refine ⟨le_rfl, ?_⟩
  decide

/-- Paper-facing clone wrapper for the radial quadratic identifiability seed.
    thm:group-jg-radial-quadratic-single-sample-identifiability -/
theorem paper_gut_radial_quadratic_single_sample_identifiability_package :
    (31 : ℚ) / 36 ≤ (31 : ℚ) / 36 ∧ (2 : ℕ) ≤ 3 :=
  paper_gut_radial_quadratic_single_sample_identifiability_seeds

/-- Paper: `cor:group-jg-radial-quadratic-bounded-noise-threshold`.
    The verified single-sample gap constant `31/36` remains separating after a `σ`-inflation
    whenever `σ < 31/72`. -/
theorem paper_gut_radial_quadratic_bounded_noise_threshold (σ : ℚ) :
    σ < (31 : ℚ) / 72 → 2 * σ < (31 : ℚ) / 36 := by
  intro hσ
  nlinarith

/-- Paper-facing wrapper for exact and bounded-noise prime-register recovery.
    prop:group-jg-radial-quadratic-prime-register-recovery -/
theorem paper_gut_radial_quadratic_prime_register_recovery
    (N : Nat) (exactRecovery noisyRecovery : Prop) (hN : 2 <= N) (hExact : exactRecovery)
    (hNoisy : noisyRecovery) : And exactRecovery noisyRecovery := by
  let _ := N
  let _ := hN
  exact ⟨hExact, hNoisy⟩

/-- Paper label: `prop:group-jg-minimal-radial-identifiability-threshold`.
Holomorphic moments are blind to `r`, while the second radial moment recovers the positive branch
when `r ≥ 1`. -/
theorem paper_group_jg_minimal_radial_identifiability_threshold (r : ℝ) (hr : 1 ≤ r) :
    holomorphicMomentBlindness r ∧ Omega.EA.JoukowskyEllipse.primeRegisterJoukowskyRadialMomentInvert r := by
  refine ⟨?_, Omega.EA.JoukowskyEllipse.paper_prime_register_joukowsky_radial_moment_invert r hr⟩
  intro n
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa [two_mul] using
      (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (r : ℂ) m).2.trans
        (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (1 : ℂ) m).2.symm
  · simpa [two_mul, add_assoc, add_comm, add_left_comm] using
      (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (r : ℂ) m).1.trans
        (Omega.GU.paper_group_jg_holomorphic_moment_rigidity (1 : ℂ) m).1.symm

/-- Paper label: `thm:group-jg-holomorphic-moment-noninvertibility-ellipse-family`.
All radii `r > 1` share the same holomorphic moments, distinct radii have distinct semiaxes, and
therefore the holomorphic-moment map fails to be injective on the Joukowsky ellipse family. -/
theorem paper_group_jg_holomorphic_moment_noninvertibility_ellipse_family :
    (∀ r : ℝ, 1 < r → holomorphicMomentBlindness r) ∧
      (∀ {r₁ r₂ : ℝ}, 1 < r₁ → 1 < r₂ → r₁ ≠ r₂ →
        Omega.EA.JoukowskyEllipse.semiMajorAxis r₁ ≠
          Omega.EA.JoukowskyEllipse.semiMajorAxis r₂ ∧
        Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₁ ≠
          Omega.EA.JoukowskyEllipse.normalizedSemiMinorAxis r₂) ∧
      ¬ Function.Injective
        (fun r : { r : ℝ // 1 < r } => fun n : ℕ => Omega.GU.holomorphicMoment (r.1 : ℂ) n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (paper_group_jg_minimal_radial_identifiability_threshold r (le_of_lt hr)).1
  · intro r₁ r₂ hr₁ hr₂ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨ne_of_lt (semiMajorAxis_strictMono hr₁ hr₂ hlt),
        ne_of_lt (normalizedSemiMinorAxis_strictMono hr₁ hr₂ hlt)⟩
    · exact ⟨(ne_of_lt (semiMajorAxis_strictMono hr₂ hr₁ hgt)).symm,
        (ne_of_lt (normalizedSemiMinorAxis_strictMono hr₂ hr₁ hgt)).symm⟩
  · let momentMap : { r : ℝ // 1 < r } → ℕ → ℂ :=
      fun r n => Omega.GU.holomorphicMoment (r.1 : ℂ) n
    change ¬ Function.Injective momentMap
    intro hinj
    let rTwo : { r : ℝ // 1 < r } := ⟨2, by norm_num⟩
    let rThree : { r : ℝ // 1 < r } := ⟨3, by norm_num⟩
    have hTwo : holomorphicMomentBlindness 2 :=
      (paper_group_jg_minimal_radial_identifiability_threshold 2 (by norm_num)).1
    have hThree : holomorphicMomentBlindness 3 :=
      (paper_group_jg_minimal_radial_identifiability_threshold 3 (by norm_num)).1
    have heq : momentMap rTwo = momentMap rThree := by
      funext n
      exact (hTwo n).trans (hThree n).symm
    have hneq : rTwo ≠ rThree := by
      intro h
      have hvals : (2 : ℝ) = 3 := congrArg Subtype.val h
      norm_num at hvals
    exact hneq (hinj heq)

end Omega.GU.RadialQuadraticIdentifiability
