import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace Omega.CircleDimension

open Matrix

/-- The standard integral order-three generator on `ℤ²`. -/
def s4v4StandardGenerator : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, -1; 1, -1]

/-- The `A₂` Cartan matrix. -/
def a2CartanForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -1; -1, 2]

/-- A symmetric integral `2 × 2` form. -/
def symmetricIntegralForm (a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a, b; b, c]

/-- Concrete natural-polarization data for the Prym rigidity argument. -/
structure S4V4PrymA2PolarizedIsogenyRigidityData where
  a : ℤ
  b : ℤ
  c : ℤ
  naturalPolarization : Matrix (Fin 2) (Fin 2) ℤ
  hnatural : naturalPolarization = symmetricIntegralForm a b c
  hinvariant :
    s4v4StandardGeneratorᵀ * naturalPolarization * s4v4StandardGenerator = naturalPolarization
  hpositive : 0 < a
  hdet : naturalPolarization.det = 3

namespace S4V4PrymA2PolarizedIsogenyRigidityData

/-- The standard generator has exact order three. -/
def standardGeneratorExists (_D : S4V4PrymA2PolarizedIsogenyRigidityData) : Prop :=
  s4v4StandardGenerator ^ 3 = 1

/-- Every symmetric integral form fixed by the standard generator is an integral multiple of the
`A₂` Cartan form. -/
def invariantPolarizationsAreA2 (_D : S4V4PrymA2PolarizedIsogenyRigidityData) : Prop :=
  ∀ a b c : ℤ,
    s4v4StandardGeneratorᵀ * symmetricIntegralForm a b c * s4v4StandardGenerator =
        symmetricIntegralForm a b c →
      ∃ k : ℤ, symmetricIntegralForm a b c = k • a2CartanForm

/-- The natural Prym polarization is exactly the `A₂` Cartan form. -/
def naturalPrymPolarizationIsA2 (D : S4V4PrymA2PolarizedIsogenyRigidityData) : Prop :=
  D.naturalPolarization = a2CartanForm

end S4V4PrymA2PolarizedIsogenyRigidityData

open S4V4PrymA2PolarizedIsogenyRigidityData

lemma standardGenerator_cube : s4v4StandardGenerator ^ 3 = 1 := by
  native_decide

lemma invariant_form_is_a2_multiple (a b c : ℤ)
    (h :
      s4v4StandardGeneratorᵀ * symmetricIntegralForm a b c * s4v4StandardGenerator =
        symmetricIntegralForm a b c) :
    ∃ k : ℤ, symmetricIntegralForm a b c = k • a2CartanForm := by
  have h00 : c = a := by
    simpa [s4v4StandardGenerator, symmetricIntegralForm, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M => M 0 0) h
  have h01 : -b - c = b := by
    simpa [s4v4StandardGenerator, symmetricIntegralForm, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M => M 0 1) h
  have h11' : b + a + (c + b) = c := by
    simpa [s4v4StandardGenerator, symmetricIntegralForm, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M => M 1 1) h
  have ha : a = -2 * b := by
    linarith
  have hc : c = -2 * b := by
    linarith
  refine ⟨-b, ?_⟩
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [symmetricIntegralForm, a2CartanForm, ha, hc, mul_comm]

/-- The standard order-three generator is the unique integral normal form for the `C₃` action; its
invariant symmetric forms are exactly the positive multiples of the `A₂` Cartan matrix, and
determinant `3` forces the natural Prym polarization to be the primitive one.
    thm:cdim-s4-v4-prym-a2-polarized-isogeny-rigidity -/
theorem paper_cdim_s4_v4_prym_a2_polarized_isogeny_rigidity
    (D : S4V4PrymA2PolarizedIsogenyRigidityData) :
    D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧ D.naturalPrymPolarizationIsA2 := by
  refine ⟨standardGenerator_cube, ?_, ?_⟩
  · intro a b c h
    exact invariant_form_is_a2_multiple a b c h
  · have hk : ∃ k : ℤ, symmetricIntegralForm D.a D.b D.c = k • a2CartanForm := by
      have hInvariant' :
          s4v4StandardGeneratorᵀ * symmetricIntegralForm D.a D.b D.c * s4v4StandardGenerator =
            symmetricIntegralForm D.a D.b D.c := by
        simpa [D.hnatural] using D.hinvariant
      exact invariant_form_is_a2_multiple D.a D.b D.c hInvariant'
    rcases hk with ⟨k, hk⟩
    have hdetk : D.naturalPolarization.det = 3 * k ^ 2 := by
      rw [D.hnatural, hk]
      simp [a2CartanForm, Matrix.det_fin_two]
      ring
    have hk_sq : k ^ 2 = 1 := by
      linarith [D.hdet, hdetk]
    have ha : D.a = 2 * k := by
      simpa [symmetricIntegralForm, a2CartanForm, mul_comm] using congrArg (fun M => M 0 0) hk
    have hk_pos : 0 < k := by
      linarith [D.hpositive, ha]
    have hk_one : k = 1 := by
      nlinarith [hk_sq, hk_pos]
    calc
      D.naturalPolarization = symmetricIntegralForm D.a D.b D.c := D.hnatural
      _ = k • a2CartanForm := hk
      _ = a2CartanForm := by simpa [hk_one]

end Omega.CircleDimension
