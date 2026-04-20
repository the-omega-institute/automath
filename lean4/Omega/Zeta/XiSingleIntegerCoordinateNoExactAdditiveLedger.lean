import Mathlib.Tactic

namespace Omega.Zeta

private lemma additive_zero
    {r : Nat} {e : (Fin r → Nat) → Int}
    (hadd : ∀ a b : Fin r → Nat, e (fun i => a i + b i) = e a + e b) :
    e 0 = 0 := by
  have h := hadd (0 : Fin r → Nat) 0
  change e 0 = e 0 + e 0 at h
  have h' := congrArg (fun z : Int => z - e 0) h
  simpa using h'.symm

private lemma additive_single_mul
    {r : Nat} {e : (Fin r → Nat) → Int}
    (hadd : ∀ a b : Fin r → Nat, e (fun i => a i + b i) = e a + e b)
    (i : Fin r) :
    ∀ n : Nat, e ((Pi.single i n : Fin r → Nat)) = (n : Int) * e (Pi.single i 1)
  | 0 => by
      simp [Pi.single, additive_zero hadd]
  | n + 1 => by
      have hsplit :
          (Pi.single i (n + 1) : Fin r → Nat) =
            (Pi.single i n : Fin r → Nat) + (Pi.single i 1 : Fin r → Nat) := by
        ext j
        by_cases h : j = i
        · subst h
          simp [Pi.single]
        · simp [Pi.single, h]
      calc
        e ((Pi.single i (n + 1) : Fin r → Nat))
            = e ((Pi.single i n : Fin r → Nat) + (Pi.single i 1 : Fin r → Nat)) := by rw [hsplit]
        _ = e (Pi.single i n) + e (Pi.single i 1) := hadd _ _
        _ = (n : Int) * e (Pi.single i 1) + e (Pi.single i 1) := by
              rw [additive_single_mul hadd i n]
        _ = ((n : Int) + 1) * e (Pi.single i 1) := by ring
        _ = ((n + 1 : Nat) : Int) * e (Pi.single i 1) := by norm_num

private lemma toNat_ne_zero_of_pos {z : Int} (hz : 0 < z) : z.toNat ≠ 0 := by
  intro h
  have hcast : ((z.toNat : Nat) : Int) = z := by
    rw [Int.toNat_of_nonneg (le_of_lt hz)]
  omega

private lemma toNat_ne_zero_of_neg {z : Int} (hz : z < 0) : (-z).toNat ≠ 0 := by
  intro h
  have hcast : (((-z).toNat : Nat) : Int) = -z := by
    rw [Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hz))]
  omega

/-- A single integer ledger cannot encode all finite-support exponent vectors additively once there
are at least two coordinates: additivity makes the ledger linear in each basis direction, and two
coordinates already force a collision on `ℕ^r`.
    thm:xi-single-integer-coordinate-no-exact-additive-ledger -/
theorem paper_xi_single_integer_coordinate_no_exact_additive_ledger (r : Nat) (hr : 2 ≤ r) :
    ¬ ∃ e : (Fin r → Nat) → Int, Function.Injective e ∧
      ∀ a b : Fin r → Nat, e (fun i => a i + b i) = e a + e b := by
  intro h
  rcases h with ⟨e, hinj, hadd⟩
  have hr0 : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
  have hr1 : 1 < r := lt_of_lt_of_le (by decide : 1 < 2) hr
  let i0 : Fin r := ⟨0, hr0⟩
  let i1 : Fin r := ⟨1, hr1⟩
  have hi01 : i0 ≠ i1 := by
    intro hEq
    have : (0 : Nat) = 1 := congrArg Fin.val hEq
    omega
  let a := e (Pi.single i0 1)
  let b := e (Pi.single i1 1)
  by_cases ha0 : a = 0
  · have hEq : e (Pi.single i0 1) = e 0 := by
      have : e (Pi.single i0 1) = 0 := by simpa [a] using ha0
      simpa [additive_zero hadd] using this
    have hVec := hinj hEq
    have hval := congrArg (fun f => f i0) hVec
    simp [Pi.single] at hval
  by_cases hb0 : b = 0
  · have hEq : e (Pi.single i1 1) = e 0 := by
      have : e (Pi.single i1 1) = 0 := by simpa [b] using hb0
      simpa [additive_zero hadd] using this
    have hVec := hinj hEq
    have hval := congrArg (fun f => f i1) hVec
    simp [Pi.single] at hval
  by_cases haPos : 0 < a
  · by_cases hbPos : 0 < b
    · let u : Fin r → Nat := Pi.single i0 b.toNat
      let v : Fin r → Nat := Pi.single i1 a.toNat
      have hu :
          e u = (b.toNat : Int) * e (Pi.single i0 1) := by
        simpa [u] using additive_single_mul hadd i0 b.toNat
      have hv :
          e v = (a.toNat : Int) * e (Pi.single i1 1) := by
        simpa [v] using additive_single_mul hadd i1 a.toNat
      have hEq : e u = e v := by
        rw [hu, hv, Int.toNat_of_nonneg (le_of_lt hbPos), Int.toNat_of_nonneg (le_of_lt haPos)]
        ring
      have huv : u ≠ v := by
        intro huv
        have h0 := congrArg (fun f => f i0) huv
        simp [u, v, Pi.single, hi01, toNat_ne_zero_of_pos hbPos] at h0
      exact huv (hinj hEq)
    · have hbNeg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbPos) hb0
      let u : Fin r → Nat := Pi.single i0 ((-b).toNat) + Pi.single i1 a.toNat
      have hu0 :
          e (Pi.single i0 ((-b).toNat)) = (((-b).toNat : Nat) : Int) * e (Pi.single i0 1) := by
        simpa using additive_single_mul hadd i0 ((-b).toNat)
      have hu1 :
          e (Pi.single i1 a.toNat) = ((a.toNat : Nat) : Int) * e (Pi.single i1 1) := by
        simpa using additive_single_mul hadd i1 a.toNat
      have hs :
          e u = e (Pi.single i0 ((-b).toNat)) + e (Pi.single i1 a.toNat) := by
        simpa [u] using hadd (Pi.single i0 ((-b).toNat)) (Pi.single i1 a.toNat)
      have hEq : e u = e 0 := by
        rw [additive_zero hadd, hs, hu0, hu1,
          Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hbNeg)),
          Int.toNat_of_nonneg (le_of_lt haPos)]
        ring
      have hu_ne : u ≠ 0 := by
        intro hu
        have h0 := congrArg (fun f => f i0) hu
        simp [u, Pi.single, hi01, toNat_ne_zero_of_neg hbNeg] at h0
      exact hu_ne (hinj hEq)
  · have haNeg : a < 0 := lt_of_le_of_ne (le_of_not_gt haPos) ha0
    by_cases hbPos : 0 < b
    · let u : Fin r → Nat := Pi.single i0 b.toNat + Pi.single i1 ((-a).toNat)
      have hu0 :
          e (Pi.single i0 b.toNat) = ((b.toNat : Nat) : Int) * e (Pi.single i0 1) := by
        simpa using additive_single_mul hadd i0 b.toNat
      have hu1 :
          e (Pi.single i1 ((-a).toNat)) = (((-a).toNat : Nat) : Int) * e (Pi.single i1 1) := by
        simpa using additive_single_mul hadd i1 ((-a).toNat)
      have hs :
          e u = e (Pi.single i0 b.toNat) + e (Pi.single i1 ((-a).toNat)) := by
        simpa [u] using hadd (Pi.single i0 b.toNat) (Pi.single i1 ((-a).toNat))
      have hEq : e u = e 0 := by
        rw [additive_zero hadd, hs, hu0, hu1, Int.toNat_of_nonneg (le_of_lt hbPos),
          Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt haNeg))]
        ring
      have hu_ne : u ≠ 0 := by
        intro hu
        have h0 := congrArg (fun f => f i1) hu
        simp [u, Pi.single, toNat_ne_zero_of_neg haNeg] at h0
      exact hu_ne (hinj hEq)
    · have hbNeg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbPos) hb0
      let u : Fin r → Nat := Pi.single i0 ((-b).toNat)
      let v : Fin r → Nat := Pi.single i1 ((-a).toNat)
      have hu :
          e u = (((-b).toNat : Nat) : Int) * e (Pi.single i0 1) := by
        simpa [u] using additive_single_mul hadd i0 ((-b).toNat)
      have hv :
          e v = (((-a).toNat : Nat) : Int) * e (Pi.single i1 1) := by
        simpa [v] using additive_single_mul hadd i1 ((-a).toNat)
      have hEq : e u = e v := by
        rw [hu, hv, Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hbNeg)),
          Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt haNeg))]
        ring
      have huv : u ≠ v := by
        intro huv
        have h0 := congrArg (fun f => f i0) huv
        simp [u, v, Pi.single, hi01, toNat_ne_zero_of_neg hbNeg] at h0
      exact huv (hinj hEq)

end Omega.Zeta
