import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Omega.Zeta.XiCayleyJoukowskyHarmonicMeasureEllipse

namespace Omega.Zeta

noncomputable section

/-- Center of the translated arcsine law for `|W_L|^2`. -/
def xi_joukowsky_modsquare_arcsine_fixedwidth_center (L : ℝ) : ℝ :=
  L + 1 / L

/-- The squared modulus of the Joukowsky image. -/
def xi_joukowsky_modsquare_arcsine_fixedwidth_modsquare (L θ : ℝ) : ℝ :=
  xiJoukowskyX L θ ^ 2 + xiJoukowskyY L θ ^ 2

/-- Support interval of the translated arcsine law for `|W_L|^2`. -/
def xi_joukowsky_modsquare_arcsine_fixedwidth_support (L : ℝ) : Set ℝ :=
  Set.Icc (xi_joukowsky_modsquare_arcsine_fixedwidth_center L - 2)
    (xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2)

/-- The affine translate of the standard arcsine density. -/
def xi_joukowsky_modsquare_arcsine_fixedwidth_density (L s : ℝ) : ℝ :=
  xiArcsineDensity (s - xi_joukowsky_modsquare_arcsine_fixedwidth_center L)

/-- Concrete fixed-width arcsine package for the Joukowsky modulus square. -/
def XiJoukowskyModsquareArcsineFixedwidthStatement (L : ℝ) : Prop :=
  (∀ θ : ℝ,
    xi_joukowsky_modsquare_arcsine_fixedwidth_modsquare L θ =
      xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2 * Real.cos (2 * θ)) ∧
    xi_joukowsky_modsquare_arcsine_fixedwidth_support L =
      Set.Icc (xiEllipseB L ^ 2) (xiEllipseA L ^ 2) ∧
    (∀ x : ℝ,
      xi_joukowsky_modsquare_arcsine_fixedwidth_density L
          (xi_joukowsky_modsquare_arcsine_fixedwidth_center L + x) =
        xiArcsineDensity x) ∧
    xiEllipseA L ^ 2 - xiEllipseB L ^ 2 = 4

private lemma xi_joukowsky_modsquare_arcsine_fixedwidth_upper_endpoint
    (L : ℝ) (hL : 1 < L) :
    xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2 = xiEllipseA L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hsqrt : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hsqrt_ne : Real.sqrt L ≠ 0 := by positivity
  calc
    xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2
        = L + 1 / L + 2 := by
          rfl
    _ = Real.sqrt L ^ 2 + 2 * (Real.sqrt L * (1 / Real.sqrt L)) + (1 / Real.sqrt L) ^ 2 := by
          rw [hsqrt, one_div_pow, hsqrt]
          have hmul : Real.sqrt L * (1 / Real.sqrt L) = 1 := by
            field_simp [hsqrt_ne]
          rw [hmul]
          ring
    _ = xiEllipseA L ^ 2 := by
          unfold xiEllipseA
          ring

private lemma xi_joukowsky_modsquare_arcsine_fixedwidth_lower_endpoint
    (L : ℝ) (hL : 1 < L) :
    xi_joukowsky_modsquare_arcsine_fixedwidth_center L - 2 = xiEllipseB L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hsqrt : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hsqrt_ne : Real.sqrt L ≠ 0 := by positivity
  calc
    xi_joukowsky_modsquare_arcsine_fixedwidth_center L - 2
        = L + 1 / L - 2 := by
          rfl
    _ = Real.sqrt L ^ 2 - 2 * (Real.sqrt L * (1 / Real.sqrt L)) + (1 / Real.sqrt L) ^ 2 := by
          rw [hsqrt, one_div_pow, hsqrt]
          have hmul : Real.sqrt L * (1 / Real.sqrt L) = 1 := by
            field_simp [hsqrt_ne]
          rw [hmul]
          ring
    _ = xiEllipseB L ^ 2 := by
          unfold xiEllipseB
          ring

private lemma xi_joukowsky_modsquare_arcsine_fixedwidth_modsquare_formula
    (L θ : ℝ) (hL : 1 < L) :
    xi_joukowsky_modsquare_arcsine_fixedwidth_modsquare L θ =
      xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2 * Real.cos (2 * θ) := by
  have hL0 : 0 ≤ L := by linarith
  have hsqrt : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hsqrt_ne : Real.sqrt L ≠ 0 := by positivity
  have hcos : Real.cos θ ^ 2 - Real.sin θ ^ 2 = Real.cos (2 * θ) := by
    nlinarith [Real.cos_two_mul θ, Real.sin_sq_add_cos_sq θ]
  calc
    xi_joukowsky_modsquare_arcsine_fixedwidth_modsquare L θ
        = (Real.sqrt L * Real.cos θ + (1 / Real.sqrt L) * Real.cos θ) ^ 2 +
            (Real.sqrt L * Real.sin θ - (1 / Real.sqrt L) * Real.sin θ) ^ 2 := by
            rfl
    _ = Real.sqrt L ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
          (1 / Real.sqrt L) ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
          2 * (Real.sqrt L * (1 / Real.sqrt L)) * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
          ring
    _ = L + 1 / L + 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
          rw [hsqrt, one_div_pow, hsqrt]
          have hmul : Real.sqrt L * (1 / Real.sqrt L) = 1 := by
            field_simp [hsqrt_ne]
          rw [hmul]
          have hsum : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
            nlinarith [Real.sin_sq_add_cos_sq θ]
          rw [hsum]
          ring
    _ = xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2 * Real.cos (2 * θ) := by
          unfold xi_joukowsky_modsquare_arcsine_fixedwidth_center
          rw [hcos]

/-- Paper label: `thm:xi-joukowsky-modsquare-arcsine-fixedwidth`. -/
theorem paper_xi_joukowsky_modsquare_arcsine_fixedwidth
    (L : ℝ) (hL : 1 < L) : XiJoukowskyModsquareArcsineFixedwidthStatement L := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ
    exact xi_joukowsky_modsquare_arcsine_fixedwidth_modsquare_formula L θ hL
  · unfold xi_joukowsky_modsquare_arcsine_fixedwidth_support
    rw [xi_joukowsky_modsquare_arcsine_fixedwidth_lower_endpoint L hL,
      xi_joukowsky_modsquare_arcsine_fixedwidth_upper_endpoint L hL]
  · intro x
    unfold xi_joukowsky_modsquare_arcsine_fixedwidth_density
      xi_joukowsky_modsquare_arcsine_fixedwidth_center
    ring_nf
  · calc
      xiEllipseA L ^ 2 - xiEllipseB L ^ 2
          = (xi_joukowsky_modsquare_arcsine_fixedwidth_center L + 2) -
              (xi_joukowsky_modsquare_arcsine_fixedwidth_center L - 2) := by
                rw [xi_joukowsky_modsquare_arcsine_fixedwidth_upper_endpoint L hL,
                  xi_joukowsky_modsquare_arcsine_fixedwidth_lower_endpoint L hL]
      _ = 4 := by ring

end

end Omega.Zeta
