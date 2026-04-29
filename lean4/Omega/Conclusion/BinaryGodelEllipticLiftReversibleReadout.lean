import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Big-endian binary value attached to a Boolean word. -/
def conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue : List Bool → Nat
  | [] => 0
  | b :: w =>
      (if b then 2 ^ w.length else 0) +
        conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w

/-- Additive lift of the binary word value along a distinguished point. -/
def conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def
    {G : Type*} [AddCommGroup G] (P : G) (w : List Bool) : G :=
  ((conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w : Int) • P)

local notation "conclusion_binary_godel_elliptic_lift_reversible_readout_phi" =>
  conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def

private lemma conclusion_binary_godel_elliptic_lift_reversible_readout_bit_append_recurrence :
    ∀ (w : List Bool) (b : Bool),
      conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue (w ++ [b]) =
        2 * conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w +
          if b then 1 else 0
  | [], b => by
      cases b <;> simp [conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue]
  | a :: w, b => by
      cases a <;>
        simp [conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue,
          conclusion_binary_godel_elliptic_lift_reversible_readout_bit_append_recurrence, pow_succ,
          Nat.mul_add, Nat.mul_comm, Nat.add_left_comm, Nat.add_comm]

private lemma conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length :
    ∀ w : List Bool,
      conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w < 2 ^ w.length
  | [] => by
      simp [conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue]
  | false :: w => by
      simpa [conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue, pow_succ,
        Nat.mul_comm] using
        (lt_trans
          (conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length w)
          (by
            have hpow : 2 ^ w.length < 2 * 2 ^ w.length := by
              calc
                2 ^ w.length = 1 * 2 ^ w.length := by simp
                _ < 2 * 2 ^ w.length := by
                    exact Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (by decide) _)
            simpa [pow_succ, Nat.mul_comm] using hpow))
  | true :: w => by
      have htail :
          conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w < 2 ^ w.length :=
        conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length w
      have hsum :
          2 ^ w.length +
              conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w <
            2 ^ w.length + 2 ^ w.length := by
        exact Nat.add_lt_add_left htail (2 ^ w.length)
      calc
        conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue (true :: w)
            = 2 ^ w.length +
                conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w := by
                  simp [conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue]
        _ < 2 ^ w.length + 2 ^ w.length := hsum
        _ = 2 ^ (List.length w + 1) := by
              rw [pow_succ]
              ring

private lemma conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_injective_of_length_eq
    {w w' : List Bool} (hlen : w.length = w'.length)
    (hval :
      conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w =
        conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w') :
    w = w' := by
  revert w'
  induction w with
  | nil =>
      intro w' hlen hval
      cases w' with
      | nil => rfl
      | cons b w' =>
          simp at hlen
  | cons b w ih =>
      intro w' hlen hval
      cases w' with
      | nil =>
          simp at hlen
      | cons b' w' =>
          have hwlen : w.length = w'.length := Nat.succ.inj hlen
          have hlt_w :
              conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w <
                2 ^ w.length :=
            conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length w
          have hlt_w' :
              conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w' <
                2 ^ w'.length :=
            conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length w'
          cases b <;> cases b' <;>
            simp [conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue, hwlen] at hval ⊢
          · exact ih hwlen hval
          · have hge : 2 ^ w.length ≤ 2 ^ w'.length +
                conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w' := by
              simp [hwlen]
            rw [hval] at hlt_w
            exact (not_lt_of_ge hge) hlt_w
          · have hge : 2 ^ w'.length ≤ 2 ^ w'.length +
                conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w := by
              simp
            rw [← hval] at hlt_w'
            exact (not_lt_of_ge hge) hlt_w'
          · have htail :
                conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w =
                  conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w' := by
              omega
            exact ih hwlen htail

/-- Paper label: `prop:conclusion-binary-godel-elliptic-lift-reversible-readout`. -/
theorem paper_conclusion_binary_godel_elliptic_lift_reversible_readout
    {G : Type*} [AddCommGroup G] (P : G) (hP : P ≠ 0) (n : Nat)
    (hinj : Function.Injective fun i : Fin (2 ^ n) => ((i.1 : Int) • P)) :
    (∀ (w : List Bool) (b : Bool),
        conclusion_binary_godel_elliptic_lift_reversible_readout_phi P (w ++ [b]) =
          (2 : Int) • conclusion_binary_godel_elliptic_lift_reversible_readout_phi P w +
            if b then P else 0) ∧
      (∀ (Q Q' : G) (b : Bool),
        Q' = ((2 : Int) • Q + if b then P else 0) →
          Q' - (2 : Int) • Q = if b then P else 0) ∧
      Function.Injective
        (fun w : {w : List Bool // w.length = n} =>
          conclusion_binary_godel_elliptic_lift_reversible_readout_phi P w.1) := by
  let _ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro w b
    have hrec :=
      conclusion_binary_godel_elliptic_lift_reversible_readout_bit_append_recurrence w b
    cases b
    · calc
        conclusion_binary_godel_elliptic_lift_reversible_readout_phi P (w ++ [false])
            = (((2 *
                    conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w : Nat) :
                  Int) • P) := by
                simp [conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def, hrec]
        _ = (2 : Int) • conclusion_binary_godel_elliptic_lift_reversible_readout_phi P w := by
              simpa [conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def, mul_comm]
                using
                  (smul_smul (2 : Int)
                    (conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w : Int) P).symm
        _ = (2 : Int) • conclusion_binary_godel_elliptic_lift_reversible_readout_phi P w + 0 := by
              simp
    · calc
        conclusion_binary_godel_elliptic_lift_reversible_readout_phi P (w ++ [true])
            = ((((2 *
                      conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w + 1 :
                    Nat) : Int)) • P) := by
                simp [conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def, hrec]
        _ = (((2 *
                    conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w : Nat) :
                  Int) • P) +
              ((1 : Int) • P) := by
                rw [show
                    (((2 *
                          conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w +
                        1 : Nat) : Int)) =
                      (((2 *
                            conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue
                              w :
                          Nat) : Int) + 1) by simp]
                rw [add_zsmul]
        _ = (2 : Int) • conclusion_binary_godel_elliptic_lift_reversible_readout_phi P w + P := by
              simpa [conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def, mul_comm]
                using
                  congrArg (fun x : G => x + P)
                    ((smul_smul (2 : Int)
                      (conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w : Int) P).symm)
  · intro Q Q' b hQ'
    simpa [hQ', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · intro w w' hphi
    let i : Fin (2 ^ n) :=
      ⟨conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w.1,
        by simpa [w.2] using
          conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length w.1⟩
    let i' : Fin (2 ^ n) :=
      ⟨conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w'.1,
        by simpa [w'.2] using
          conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_lt_pow_length w'.1⟩
    have hscalar : ((i.1 : Int) • P) = ((i'.1 : Int) • P) := by
      simpa [i, i', conclusion_binary_godel_elliptic_lift_reversible_readout_phi_def] using hphi
    have hi : i = i' := hinj hscalar
    have hval :
        conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w.1 =
          conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue w'.1 := by
      simpa [i, i'] using congrArg Fin.val hi
    have hword : w.1 = w'.1 :=
      conclusion_binary_godel_elliptic_lift_reversible_readout_binaryValue_injective_of_length_eq
        (by simpa [w.2, w'.2]) hval
    exact Subtype.ext hword

end Omega.Conclusion
