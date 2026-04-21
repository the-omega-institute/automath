import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Omega.EA.GodelLogBusemann
import Omega.GU.GroupJGPrimeRegisterPhaseBohrDense

namespace Omega.EA.JoukowskyEllipse

open scoped BigOperators

/-- Diagonal action `diag(r, r⁻¹) · (x, y) = (r·x, r⁻¹·y)`.
    thm:prime-register-dense-ellipticization -/
noncomputable def diagAction (r x y : ℝ) : ℝ × ℝ := (r * x, r⁻¹ * y)

/-- The diagonal action sends the unit circle to the ellipse with semi-axes `(r, r⁻¹)`.
    thm:prime-register-dense-ellipticization -/
theorem diag_maps_circle_to_ellipse (r x y : ℝ) (hr : r ≠ 0)
    (h : x^2 + y^2 = 1) :
    ((diagAction r x y).1 / r)^2 + ((diagAction r x y).2 * r)^2 = 1 := by
  unfold diagAction
  simp only
  have hx : (r * x) / r = x := by field_simp
  have hy : (r⁻¹ * y) * r = y := by field_simp
  rw [hx, hy]
  exact h

/-- Ellipse axis product equals `1`.
    thm:prime-register-dense-ellipticization -/
theorem ellipse_axes_product (r : ℝ) (hr : r ≠ 0) : r * r⁻¹ = 1 :=
  mul_inv_cancel₀ hr

/-- Axis ratio equals `r²` for `r ≥ 1`.
    thm:prime-register-dense-ellipticization -/
theorem axis_ratio_eq_r_sq (r : ℝ) (hr : 1 ≤ r) : r / r⁻¹ = r^2 := by
  have h0 : r ≠ 0 := by linarith
  field_simp

/-- Positive square root is unique.
    thm:prime-register-dense-ellipticization -/
theorem r_unique_from_sq (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (heq : r₁^2 = r₂^2) : r₁ = r₂ := by
  nlinarith [sq_nonneg (r₁ - r₂), sq_nonneg (r₁ + r₂)]

/-- Ellipse area equals `π` (semi-axis product times `π`).
    thm:prime-register-dense-ellipticization -/
theorem ellipse_area_eq_pi (r : ℝ) (hr : r ≠ 0) :
    Real.pi * r * r⁻¹ = Real.pi := by
  rw [mul_assoc, mul_inv_cancel₀ hr, mul_one]

/-- Paper package (part 2): ellipticisation axis/ratio/area identities.
    thm:prime-register-dense-ellipticization -/
theorem paper_prime_register_dense_ellipticization_part2
    (r : ℝ) (hr : 1 ≤ r) :
    r * r⁻¹ = 1 ∧ r / r⁻¹ = r^2 ∧ Real.pi * r * r⁻¹ = Real.pi := by
  have h0 : r ≠ 0 := by linarith
  exact ⟨ellipse_axes_product r h0, axis_ratio_eq_r_sq r hr, ellipse_area_eq_pi r h0⟩

/-- Full paper package: the two-prime logarithmic subgroup is dense, and the corresponding
normalized ellipse has unit area with axis product `1` and axis ratio `r^2`.
    thm:prime-register-dense-ellipticization -/
theorem paper_prime_register_dense_ellipticization (r : ℝ) (hr : 1 ≤ r) :
    Dense (AddSubgroup.closure {Real.log (2 : ℝ), Real.log (3 : ℝ)} : Set ℝ) ∧
      r * r⁻¹ = 1 ∧ r / r⁻¹ = r ^ 2 ∧ Real.pi * r * r⁻¹ = Real.pi := by
  have hdense :
      Dense (AddSubgroup.closure {Real.log (2 : ℝ), Real.log (3 : ℝ)} : Set ℝ) := by
    simpa [Omega.GU.GroupJGPrimeRegisterPhaseData.phaseImageDense] using
      Omega.GU.paper_group_jg_prime_register_phase_bohr_dense ⟨1, one_ne_zero⟩
  exact ⟨hdense, (paper_prime_register_dense_ellipticization_part2 r hr)⟩

/-- The second radial moment of the normalized Joukowsky ellipse. -/
noncomputable def joukowskySecondRadialMoment (r : ℝ) : ℝ :=
  r ^ 2 + (r⁻¹) ^ 2

/-- The second radial moment determines the branch parameter in the normalized regime `r ≥ 1`. -/
noncomputable def primeRegisterJoukowskyRadialMomentInvert (r : ℝ) : Prop :=
  joukowskySecondRadialMoment r = r ^ 2 + (r⁻¹) ^ 2 ∧
    r = Real.sqrt ((joukowskySecondRadialMoment r +
      Real.sqrt (joukowskySecondRadialMoment r ^ 2 - 4)) / 2)

/-- The second radial moment `R₂(r) = r² + r⁻²` inverts to the positive branch `r` under the
normalization `r ≥ 1`.
    prop:prime-register-joukowsky-radial-moment-invert -/
theorem paper_prime_register_joukowsky_radial_moment_invert (r : Real) (hr : 1 <= r) :
    primeRegisterJoukowskyRadialMomentInvert r := by
  have h0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h0ne : r ≠ 0 := ne_of_gt h0
  have hdiff_nonneg : 0 ≤ r ^ 2 - (r⁻¹) ^ 2 := by
    have hr2_ge : 1 ≤ r ^ 2 := by nlinarith
    have hpow : 1 ≤ r ^ 4 := by nlinarith
    have hmul_nonneg : 0 ≤ r ^ 4 - 1 := by linarith
    have hmul :
        r ^ 2 * (r ^ 2 - (r⁻¹) ^ 2) = r ^ 4 - 1 := by
      field_simp [h0ne]
    have : 0 ≤ r ^ 2 * (r ^ 2 - (r⁻¹) ^ 2) := by rw [hmul]; exact hmul_nonneg
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using this) (sq_pos_of_pos h0)
  refine ⟨rfl, ?_⟩
  have hsqr :
      Real.sqrt (joukowskySecondRadialMoment r ^ 2 - 4) = r ^ 2 - (r⁻¹) ^ 2 := by
    unfold joukowskySecondRadialMoment
    rw [show (r ^ 2 + (r⁻¹) ^ 2) ^ 2 - 4 = (r ^ 2 - (r⁻¹) ^ 2) ^ 2 by
      field_simp [h0ne]
      ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hdiff_nonneg]
  have hinner :
      (joukowskySecondRadialMoment r + Real.sqrt (joukowskySecondRadialMoment r ^ 2 - 4)) / 2
        = r ^ 2 := by
    have hsqr' : Real.sqrt ((r ^ 2 + (r⁻¹) ^ 2) ^ 2 - 4) = r ^ 2 - (r⁻¹) ^ 2 := by
      simpa [joukowskySecondRadialMoment] using hsqr
    unfold joukowskySecondRadialMoment
    rw [hsqr']
    field_simp
    ring
  rw [hinner, Real.sqrt_sq (show 0 ≤ r by linarith)]

/-- The normalized Joukowsky semi-major axis. -/
noncomputable def semiMajorAxis (r : ℝ) : ℝ :=
  r + r⁻¹

/-- The normalized Joukowsky semi-minor axis in the regime `r ≥ 1`. -/
noncomputable def normalizedSemiMinorAxis (r : ℝ) : ℝ :=
  r - r⁻¹

/-- The unordered semi-minor axis, invariant under `r ↦ r⁻¹`. -/
noncomputable def semiMinorAxis (r : ℝ) : ℝ :=
  |normalizedSemiMinorAxis r|

/-- A point on the normalized Joukowsky ellipse. -/
noncomputable def joukowskyEllipsePoint (r θ : ℝ) : ℝ × ℝ :=
  (semiMajorAxis r * Real.cos θ, normalizedSemiMinorAxis r * Real.sin θ)

/-- The radius-parametrized Joukowsky ellipse family. Multiplication is transport of the radius
parameter, matching `E_r ⊙ E_s = E_{rs}` from the paper statement. -/
structure GodelJoukowskyEllipse where
  radius : ℝ

namespace GodelJoukowskyEllipse

@[ext] theorem ext {E F : GodelJoukowskyEllipse} (h : E.radius = F.radius) : E = F := by
  cases E
  cases F
  cases h
  rfl

instance : One GodelJoukowskyEllipse := ⟨⟨1⟩⟩

instance : Mul GodelJoukowskyEllipse := ⟨fun E F => ⟨E.radius * F.radius⟩⟩

instance : CommMonoid GodelJoukowskyEllipse where
  one := 1
  mul := (· * ·)
  mul_assoc a b c := by
    cases a with
    | mk ra =>
      cases b with
      | mk rb =>
        cases c with
        | mk rc =>
          change GodelJoukowskyEllipse.mk ((ra * rb) * rc) =
            GodelJoukowskyEllipse.mk (ra * (rb * rc))
          simp [mul_assoc]
  one_mul a := by
    cases a with
    | mk ra =>
      change GodelJoukowskyEllipse.mk (1 * ra) = GodelJoukowskyEllipse.mk ra
      simp
  mul_one a := by
    cases a with
    | mk ra =>
      change GodelJoukowskyEllipse.mk (ra * 1) = GodelJoukowskyEllipse.mk ra
      simp
  mul_comm a b := by
    cases a with
    | mk ra =>
      cases b with
      | mk rb =>
        change GodelJoukowskyEllipse.mk (ra * rb) = GodelJoukowskyEllipse.mk (rb * ra)
        simp [mul_comm]

end GodelJoukowskyEllipse

lemma godelScale_one_le (a : ℕ →₀ ℕ) (primes : ℕ → ℝ) (hprimes : ∀ p, 1 ≤ primes p) :
    1 ≤ Omega.EA.godelScale a primes := by
  classical
  unfold Omega.EA.godelScale
  simpa using
    (Finset.one_le_prod (s := a.support) (f := fun p => primes p ^ a p)
      (fun p => one_le_pow₀ (hprimes p)))

/-- The ellipse family attached to a positive prime-scale map. -/
noncomputable def godelJoukowskyEllipseHom
    (primes : ℕ → ℝ) (hprimes : ∀ p, 1 ≤ primes p) :
    Multiplicative (ℕ →₀ ℕ) →* GodelJoukowskyEllipse where
  toFun a := ⟨Omega.EA.godelScale (Multiplicative.toAdd a) primes⟩
  map_one' := by
    ext
    simpa using Omega.EA.godelScale_zero primes
  map_mul' := by
    intro a b
    ext
    have hab_pos : ∀ p ∈ (Multiplicative.toAdd (a * b)).support, 0 < primes p := by
      intro p hp
      exact lt_of_lt_of_le zero_lt_one (hprimes p)
    have ha_pos : ∀ p ∈ (Multiplicative.toAdd a).support, 0 < primes p := by
      intro p hp
      exact lt_of_lt_of_le zero_lt_one (hprimes p)
    have hb_pos : ∀ p ∈ (Multiplicative.toAdd b).support, 0 < primes p := by
      intro p hp
      exact lt_of_lt_of_le zero_lt_one (hprimes p)
    simpa using Omega.EA.godelScale_add
      (Multiplicative.toAdd a) (Multiplicative.toAdd b) primes hab_pos ha_pos hb_pos

/-- Paper-facing Gödel-Joukowsky ellipse package: the normalized boundary parameterization obeys
the explicit ellipse equation, `r` and `r⁻¹` define the same unordered semiaxes, the normalized
semi-axes recover `r` by `A(r) + B(r) = 2r`, and the map `a ↦ E_{G(a)}` is a commutative monoid
homomorphism. `prop:prime-register-godel-joukowsky-ellipse` -/
theorem paper_prime_register_godel_joukowsky_ellipse
    (primes : ℕ → ℝ) (hprimes : ∀ p, 1 ≤ primes p) :
    (∀ {r θ : ℝ}, 1 < r →
      let w := joukowskyEllipsePoint r θ
      (w.1 / semiMajorAxis r) ^ 2 + (w.2 / normalizedSemiMinorAxis r) ^ 2 = 1) ∧
    (∀ {r : ℝ}, 0 < r →
      semiMajorAxis r = semiMajorAxis r⁻¹ ∧ semiMinorAxis r = semiMinorAxis r⁻¹) ∧
    (∀ {r : ℝ}, 1 ≤ r → r = (semiMajorAxis r + normalizedSemiMinorAxis r) / 2) ∧
    ∃ Φ : Multiplicative (ℕ →₀ ℕ) →* GodelJoukowskyEllipse,
      (∀ a, (Φ (Multiplicative.ofAdd a)).radius = Omega.EA.godelScale a primes) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r θ hr
    dsimp [joukowskyEllipsePoint]
    have hApos : 0 < semiMajorAxis r := by
      unfold semiMajorAxis
      positivity
    have hA : semiMajorAxis r ≠ 0 := hApos.ne'
    have hr0 : r ≠ 0 := by linarith
    have hB : normalizedSemiMinorAxis r ≠ 0 := by
      unfold normalizedSemiMinorAxis
      intro h
      have hsq : r ^ 2 = 1 := by
        field_simp [hr0] at h
        nlinarith
      have : r = 1 := by
        nlinarith [sq_nonneg (r - 1), hsq]
      linarith
    have hcos : semiMajorAxis r * Real.cos θ / semiMajorAxis r = Real.cos θ := by
      field_simp [hA]
    have hsin : normalizedSemiMinorAxis r * Real.sin θ / normalizedSemiMinorAxis r = Real.sin θ := by
      field_simp [hB]
    rw [hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · intro r hr
    constructor
    · unfold semiMajorAxis
      have hr0 : r ≠ 0 := ne_of_gt hr
      field_simp [hr0]
      ring
    · unfold semiMinorAxis normalizedSemiMinorAxis
      have hr0 : r ≠ 0 := ne_of_gt hr
      rw [show (r⁻¹)⁻¹ = r by field_simp [hr0], abs_sub_comm]
  · intro r hr
    have hr0 : r ≠ 0 := by linarith
    unfold semiMajorAxis normalizedSemiMinorAxis
    field_simp [hr0]
    ring
  · refine ⟨godelJoukowskyEllipseHom primes hprimes, ?_⟩
    intro a
    rfl

end Omega.EA.JoukowskyEllipse
