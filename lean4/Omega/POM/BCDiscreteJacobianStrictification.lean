import Mathlib.Tactic
import Omega.POM.BeckChevalleyAmgmDefectIdentity

namespace Omega.POM

noncomputable section

/-- The middle-layer naive lift `L_g` in the concrete two-fiber Beck-Chevalley model. -/
noncomputable def middleUniformLift : Bool → ℝ
  | false => 1 / 2
  | true => 1 / 2

/-- The corrected discrete-Jacobian lift `\tilde L_{g,f}` in the concrete two-fiber model. -/
noncomputable def strictifiedMiddleLift (a b : ℕ) : Bool → ℝ
  | false => a / ((a : ℝ) + b)
  | true => b / ((a : ℝ) + b)

/-- Lift a two-point distribution to the two-fiber microstate space by distributing uniformly on
each `f`-fiber. -/
noncomputable def liftAlongTwoFiber (a b : ℕ) (π : Bool → ℝ) : TwoFiberSpace a b → ℝ
  | Sum.inl _ => π false / a
  | Sum.inr _ => π true / b

/-- Concrete Markov-kernel predicate on the two-point middle layer. -/
def TwoPointMarkovKernel (K : Bool → ℝ) : Prop :=
  0 ≤ K false ∧ 0 ≤ K true ∧ K false + K true = 1

lemma liftAlongTwoFiber_middleUniformLift (a b : ℕ) :
    liftAlongTwoFiber a b middleUniformLift = sequentialUniformLift a b := by
  funext x
  rcases x with _ | _
  · simp [liftAlongTwoFiber, middleUniformLift, sequentialUniformLift, div_eq_mul_inv]
    ring
  · simp [liftAlongTwoFiber, middleUniformLift, sequentialUniformLift, div_eq_mul_inv]
    ring

lemma liftAlongTwoFiber_strictifiedMiddleLift (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    liftAlongTwoFiber a b (strictifiedMiddleLift a b) = directUniformLift a b := by
  funext x
  rcases x with _ | _
  · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
    simp [liftAlongTwoFiber, strictifiedMiddleLift, directUniformLift]
    field_simp [haR, hbR.ne']
  · have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    simp [liftAlongTwoFiber, strictifiedMiddleLift, directUniformLift]
    field_simp [haR.ne', hbR]

lemma strictifiedMiddleLift_unique (a b : ℕ) (ha : 0 < a) (hb : 0 < b) {K : Bool → ℝ}
    (hLift : liftAlongTwoFiber a b K = directUniformLift a b) :
    K = strictifiedMiddleLift a b := by
  funext t
  cases t
  · let i0 : Fin a := ⟨0, ha⟩
    have h0 : K false / a = 1 / ((a : ℝ) + b) := by
      simpa [liftAlongTwoFiber, directUniformLift] using congrFun hLift (Sum.inl i0)
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
    calc
      K false = (1 / ((a : ℝ) + b)) * a := by
        exact (div_eq_iff haR).mp h0
      _ = strictifiedMiddleLift a b false := by
        simp [strictifiedMiddleLift]
        ring
  · let j0 : Fin b := ⟨0, hb⟩
    have h1 : K true / b = 1 / ((a : ℝ) + b) := by
      simpa [liftAlongTwoFiber, directUniformLift] using congrFun hLift (Sum.inr j0)
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
    calc
      K true = (1 / ((a : ℝ) + b)) * b := by
        exact (div_eq_iff hbR).mp h1
      _ = strictifiedMiddleLift a b true := by
        simp [strictifiedMiddleLift]
        ring

lemma klDiv_middle_strictified (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    klDiv middleUniformLift (strictifiedMiddleLift a b) = twoFiberAmgmDefect a b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsum :
      klDiv middleUniformLift (strictifiedMiddleLift a b) =
        (1 / 2 : ℝ) * Real.log (((1 / 2 : ℝ)) / (a / ((a : ℝ) + b))) +
          (1 / 2 : ℝ) * Real.log (((1 / 2 : ℝ)) / (b / ((a : ℝ) + b))) := by
    rw [klDiv]
    simp [middleUniformLift, strictifiedMiddleLift]
    ring
  have hRatioA : (((1 / 2 : ℝ)) / (a / ((a : ℝ) + b))) = ((a : ℝ) + b) / (2 * (a : ℝ)) := by
    field_simp [haR.ne', hbR.ne']
  have hRatioB : (((1 / 2 : ℝ)) / (b / ((a : ℝ) + b))) = ((a : ℝ) + b) / (2 * (b : ℝ)) := by
    field_simp [haR.ne', hbR.ne']
  have hPosA : 0 < ((a : ℝ) + b) / (2 * (a : ℝ)) := by positivity
  have hPosB : 0 < ((a : ℝ) + b) / (2 * (b : ℝ)) := by positivity
  have hProd :
      (((a : ℝ) + b) / (2 * (a : ℝ))) * (((a : ℝ) + b) / (2 * (b : ℝ))) =
        (((a : ℝ) + b) ^ 2) / (4 * (a : ℝ) * b) := by
    field_simp [haR.ne', hbR.ne']
    ring
  calc
    klDiv middleUniformLift (strictifiedMiddleLift a b)
        = (1 / 2 : ℝ) * Real.log (((1 / 2 : ℝ)) / (a / ((a : ℝ) + b))) +
            (1 / 2 : ℝ) * Real.log (((1 / 2 : ℝ)) / (b / ((a : ℝ) + b))) := hsum
    _ = (1 / 2 : ℝ) * Real.log (((a : ℝ) + b) / (2 * (a : ℝ))) +
          (1 / 2 : ℝ) * Real.log (((a : ℝ) + b) / (2 * (b : ℝ))) := by
      rw [hRatioA, hRatioB]
    _ = (Real.log (((a : ℝ) + b) / (2 * (a : ℝ))) +
          Real.log (((a : ℝ) + b) / (2 * (b : ℝ)))) / 2 := by
      ring
    _ = (Real.log ((((a : ℝ) + b) / (2 * (a : ℝ))) *
          (((a : ℝ) + b) / (2 * (b : ℝ))))) / 2 := by
      rw [← Real.log_mul hPosA.ne' hPosB.ne']
    _ = twoFiberAmgmDefect a b := by
      rw [hProd, twoFiberAmgmDefect]

/-- Concrete two-fiber Beck-Chevalley strictification: the corrected middle lift is the unique
kernel whose `f`-lift agrees with the direct lift, and the resulting KL defect is the same AM-GM
defect already computed on the microstate side.
    thm:pom-bc-discrete-jacobian-strictification -/
theorem paper_pom_bc_discrete_jacobian_strictification (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    liftAlongTwoFiber a b (strictifiedMiddleLift a b) = directUniformLift a b ∧
      (∀ K : Bool → ℝ, TwoPointMarkovKernel K →
        liftAlongTwoFiber a b K = directUniformLift a b → K = strictifiedMiddleLift a b) ∧
      klDiv (sequentialUniformLift a b) (directUniformLift a b) =
        klDiv middleUniformLift (strictifiedMiddleLift a b) ∧
      klDiv middleUniformLift (strictifiedMiddleLift a b) = twoFiberAmgmDefect a b := by
  have hComm := liftAlongTwoFiber_strictifiedMiddleLift a b ha hb
  have hMidKL : klDiv middleUniformLift (strictifiedMiddleLift a b) = twoFiberAmgmDefect a b :=
    klDiv_middle_strictified a b ha hb
  rcases paper_pom_bc_amgm_defect_identity a b ha hb with ⟨_, hMicroKL, _⟩
  refine ⟨hComm, ?_, ?_, hMidKL⟩
  · intro K _ hLift
    exact strictifiedMiddleLift_unique a b ha hb hLift
  · exact hMicroKL.trans hMidKL.symm

end

end Omega.POM
