import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-level Lee--Yang address tower: each level comes with a canonical splitting into
one of five sheets and a binary prefix, and the truncation maps respect that splitting. -/
structure ConclusionLeyangCanonicalAddressData where
  Level : ℕ → Type
  truncate : ∀ {m n : ℕ}, m ≤ n → Level n → Level m
  sheetEquiv : ∀ n : ℕ, Level n ≃ Fin 5 × (Fin n → Bool)
  truncate_compatible :
    ∀ {m n : ℕ} (h : m ≤ n) (a : Level n),
      sheetEquiv m (truncate h a) =
        ((sheetEquiv n a).1, fun i => (sheetEquiv n a).2 (Fin.castLE h i))

namespace ConclusionLeyangCanonicalAddressData

/-- Binary prefixes of length `n`. -/
abbrev BinaryLayer (n : ℕ) := Fin n → Bool

/-- Restriction of a longer binary prefix to a shorter one. -/
def binaryRestrict {m n : ℕ} (h : m ≤ n) (w : BinaryLayer n) : BinaryLayer m :=
  fun i => w (Fin.castLE h i)

/-- The inverse limit of the Lee--Yang finite address tower. -/
def AddressInverseLimit (D : ConclusionLeyangCanonicalAddressData) :=
  {a : ∀ n : ℕ, D.Level n // ∀ m n : ℕ, (h : m ≤ n) → D.truncate h (a n) = a m}

/-- The inverse limit of the compatible binary prefix system. -/
def T2 (_D : ConclusionLeyangCanonicalAddressData) :=
  {w : ∀ n : ℕ, BinaryLayer n // ∀ m n : ℕ, (h : m ≤ n) → binaryRestrict h (w n) = w m}

/-- The address inverse limit splits canonically as a discrete five-sheet choice and a compatible
binary inverse-limit coordinate. -/
def DiscreteContinuousSplitting (D : ConclusionLeyangCanonicalAddressData) : Prop :=
  Nonempty (D.AddressInverseLimit ≃ Fin 5 × D.T2)

/-- The finite-level sheet equivalences induce an equivalence on inverse limits. -/
def addressInverseLimitEquiv
    (D : ConclusionLeyangCanonicalAddressData) : D.AddressInverseLimit ≃ Fin 5 × D.T2 where
  toFun a :=
    let binaryFamily : ∀ n : ℕ, BinaryLayer n := fun n => (D.sheetEquiv n (a.1 n)).2
    let hbinary : ∀ m n : ℕ, (h : m ≤ n) → binaryRestrict h (binaryFamily n) = binaryFamily m :=
      by
        intro m n h
        calc
          binaryRestrict h (binaryFamily n)
              = (D.sheetEquiv m (D.truncate h (a.1 n))).2 := by
                  simpa [binaryFamily, binaryRestrict] using
                    (congrArg Prod.snd (D.truncate_compatible h (a.1 n))).symm
          _ = (D.sheetEquiv m (a.1 m)).2 := by rw [a.2 m n h]
    ((D.sheetEquiv 0 (a.1 0)).1, ⟨binaryFamily, hbinary⟩)
  invFun y :=
    ⟨fun n => (D.sheetEquiv n).symm (y.1, y.2.1 n), by
      intro m n h
      apply (D.sheetEquiv m).injective
      calc
        D.sheetEquiv m (D.truncate h ((D.sheetEquiv n).symm (y.1, y.2.1 n)))
            = (y.1, binaryRestrict h (y.2.1 n)) := by
                simpa [binaryRestrict] using D.truncate_compatible h ((D.sheetEquiv n).symm
                  (y.1, y.2.1 n))
        _ = (y.1, y.2.1 m) := by rw [y.2.2 m n h]
        _ = D.sheetEquiv m ((D.sheetEquiv m).symm (y.1, y.2.1 m)) := by
              symm
              exact (D.sheetEquiv m).apply_symm_apply (y.1, y.2.1 m)⟩
  left_inv a := by
    apply Subtype.ext
    funext n
    apply (D.sheetEquiv n).injective
    have hsheet :
        (D.sheetEquiv 0 (a.1 0)).1 = (D.sheetEquiv n (a.1 n)).1 := by
      have hcompat := D.truncate_compatible (Nat.zero_le n) (a.1 n)
      rw [a.2 0 n (Nat.zero_le n)] at hcompat
      exact congrArg Prod.fst hcompat
    simp [hsheet]
  right_inv y := by
    rcases y with ⟨sheet, w⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      funext n
      funext i
      simp

end ConclusionLeyangCanonicalAddressData

open ConclusionLeyangCanonicalAddressData

/-- Paper label: `thm:conclusion-leyang-canonical-address-discrete-continuous-splitting`. The
finite Lee--Yang address tower splits at each level into a five-sheet choice and a binary prefix,
and passing to the inverse limit yields the canonical decomposition `Fin 5 × T2`. -/
theorem paper_conclusion_leyang_canonical_address_discrete_continuous_splitting
    (D : ConclusionLeyangCanonicalAddressData) : D.DiscreteContinuousSplitting := by
  exact ⟨D.addressInverseLimitEquiv⟩

end Omega.Conclusion
