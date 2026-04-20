import Mathlib.Tactic
import Omega.Conclusion.EventEllipseGoldenMinimal

namespace Omega.Conclusion

open Matrix
open Omega.Conclusion.EventEllipseGoldenMinimal

/-- Coordinate swap matrix. -/
def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The continued-fraction digit matrix extracted from the shear seed `J * L` and repeated
left-shearing by `R`. -/
def digitMatrix (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![(n + 2 : ℝ), 1; 1, 0]

/-- Base anchor vector. -/
def ellipseAnchor0 : Fin 2 → ℝ := ![(1 : ℝ), 0]

/-- The matrix-transported anchor vector attached to a word. -/
def ellipseAnchor : List ℕ → Fin 2 → ℝ
  | [] => ellipseAnchor0
  | n :: w => digitMatrix n *ᵥ ellipseAnchor w

/-- The ellipse package attached to a word; for this theorem we retain the distinguished anchor
point of the associated matrix transport. -/
def ellipseOfWord (w : List ℕ) : Set (Fin 2 → ℝ) := {ellipseAnchor w}

private def wordCode : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | n :: w =>
      let c := wordCode w
      ((n + 2) * c.1 + c.2, c.1)

private theorem wordCode_pos : ∀ w : List ℕ, 0 < (wordCode w).1
  | [] => by decide
  | n :: w => by
      dsimp [wordCode]
      exact Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos (n + 1)) (wordCode_pos w)) _

private theorem wordCode_tail_lt_head : ∀ w : List ℕ, (wordCode w).2 < (wordCode w).1
  | [] => by decide
  | n :: w => by
      dsimp [wordCode]
      have hw : 0 < (wordCode w).1 := wordCode_pos w
      have hmul : (wordCode w).1 < (n + 2) * (wordCode w).1 := by
        calc
          (wordCode w).1 = 1 * (wordCode w).1 := by simp
          _ < (n + 2) * (wordCode w).1 := by
            exact Nat.mul_lt_mul_of_pos_right (by omega) hw
      exact lt_of_lt_of_le hmul (Nat.le_add_right _ _)

private theorem wordCode_injective : Function.Injective wordCode := by
  intro u
  induction u with
  | nil =>
      intro v h
      cases v with
      | nil => rfl
      | cons n w =>
          have hsnd := congrArg Prod.snd h
          simp [wordCode] at hsnd
          exfalso
          exact (Nat.ne_of_gt (wordCode_pos w)) hsnd.symm
  | cons n u ihu =>
      intro v h
      cases v with
      | nil =>
          have hsnd := congrArg Prod.snd h.symm
          simp [wordCode] at hsnd
          exfalso
          exact (Nat.ne_of_gt (wordCode_pos u)) hsnd.symm
      | cons m v =>
          have hsnd := congrArg Prod.snd h
          have hfst := congrArg Prod.fst h
          simp [wordCode] at hsnd hfst
          have huv : (wordCode u).1 = (wordCode v).1 := hsnd
          have hu_pos : 0 < (wordCode u).1 := wordCode_pos u
          have hu_lt : (wordCode u).2 < (wordCode u).1 := wordCode_tail_lt_head u
          have hv_lt : (wordCode v).2 < (wordCode v).1 := wordCode_tail_lt_head v
          have hfst' :
              (n + 2) * (wordCode u).1 + (wordCode u).2 =
                (m + 2) * (wordCode u).1 + (wordCode v).2 := by
            simpa [huv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfst
          have hv_lt' : (wordCode v).2 < (wordCode u).1 := by
            simpa [huv] using hv_lt
          have hn : n + 2 = m + 2 := by
            have hdiv := congrArg (fun t : ℕ => t / (wordCode u).1) hfst'
            have hdiv' :
                ((n + 2) * (wordCode u).1 + (wordCode u).2) / (wordCode u).1 =
                  ((m + 2) * (wordCode u).1 + (wordCode v).2) / (wordCode u).1 := by
              simpa [Nat.add_comm] using hdiv
            rw [Nat.add_comm ((n + 2) * (wordCode u).1) (wordCode u).2,
              Nat.mul_comm (n + 2) (wordCode u).1,
              Nat.add_mul_div_left _ _ hu_pos, Nat.div_eq_of_lt hu_lt, Nat.zero_add] at hdiv'
            rw [Nat.add_comm ((m + 2) * (wordCode u).1) (wordCode v).2,
              Nat.mul_comm (m + 2) (wordCode u).1,
              Nat.add_mul_div_left _ _ hu_pos, Nat.div_eq_of_lt hv_lt', Nat.zero_add] at hdiv'
            exact hdiv'
          have hr' : (wordCode u).2 = (wordCode v).2 := by
            have hmod := congrArg (fun t : ℕ => t % (wordCode u).1) hfst'
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt hu_lt, Nat.mod_eq_of_lt hv_lt'] using hmod
          have hn' : n = m := by omega
          have hu_eq : wordCode u = wordCode v := by
            exact Prod.ext huv hr'
          have huw : u = v := ihu hu_eq
          subst hn'
          subst huw
          rfl

private theorem digitMatrix_mulVec_code (n a b : ℕ) :
    digitMatrix n *ᵥ ![(a : ℝ), (b : ℝ)] = ![(((n + 2) * a + b : ℕ) : ℝ), (a : ℝ)] := by
  ext i
  fin_cases i
  · simp [digitMatrix, Matrix.mulVec, add_comm, mul_comm]
  · simp [digitMatrix, Matrix.mulVec]

private theorem ellipseAnchor_eq_wordCode : ∀ w : List ℕ,
    ellipseAnchor w = ![((wordCode w).1 : ℝ), ((wordCode w).2 : ℝ)]
  | [] => by
      ext i
      fin_cases i
      · simp [ellipseAnchor, ellipseAnchor0, wordCode]
      · simp [ellipseAnchor, ellipseAnchor0, wordCode]
  | n :: w => by
      rw [ellipseAnchor, ellipseAnchor_eq_wordCode w]
      simpa [wordCode] using
        digitMatrix_mulVec_code n (wordCode w).1 (wordCode w).2

private theorem ellipseAnchor_injective : Function.Injective ellipseAnchor := by
  intro u v h
  have h0 : ((wordCode u).1 : ℝ) = (wordCode v).1 := by
    simpa [ellipseAnchor_eq_wordCode] using congrArg (fun x : Fin 2 → ℝ => x 0) h
  have h1 : ((wordCode u).2 : ℝ) = (wordCode v).2 := by
    simpa [ellipseAnchor_eq_wordCode] using congrArg (fun x : Fin 2 → ℝ => x 1) h
  have hcode : wordCode u = wordCode v := by
    exact Prod.ext (Nat.cast_inj.mp h0) (Nat.cast_inj.mp h1)
  exact wordCode_injective hcode

/-- The matrix-based ellipse anchor is lossless: equal anchor sets come from equal words. -/
theorem paper_conclusion_elliptic_lossless_lift :
    Function.Injective (ellipseOfWord : List ℕ → Set (Fin 2 → ℝ)) := by
  intro u v h
  have hu : ellipseAnchor u ∈ ellipseOfWord u := by
    simp [ellipseOfWord]
  rw [h] at hu
  have huv : ellipseAnchor u = ellipseAnchor v := by
    simpa [ellipseOfWord] using hu
  exact ellipseAnchor_injective huv

end Omega.Conclusion
