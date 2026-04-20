import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The Fibonacci modulus `F_{m+2}` used by the single-coordinate affine-difference model. -/
def foldFiberSingleCoordinateAffineDifferenceModulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The residue shift `F_{k+1}` caused by flipping the selected coordinate. -/
def foldFiberSingleCoordinateAffineDifferenceShift (m k : ℕ) :
    ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m) :=
  (Nat.fib (k + 1) : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m))

/-- A concrete single-coordinate state consists of a base residue together with the chosen bit. -/
def foldFiberSingleCoordinateState (m : ℕ) :=
  ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m) × Bool

instance foldFiberSingleCoordinateAffineDifferenceModulus_neZero (m : ℕ) :
    NeZero (foldFiberSingleCoordinateAffineDifferenceModulus m) where
  out := by
    unfold foldFiberSingleCoordinateAffineDifferenceModulus
    exact Nat.ne_of_gt (Nat.fib_pos.2 (by omega))

instance foldFiberSingleCoordinateStateFintype (m : ℕ) :
    Fintype (foldFiberSingleCoordinateState m) := by
  dsimp [foldFiberSingleCoordinateState]
  infer_instance

/-- The total residue of a state is the base residue plus the affine contribution of the bit. -/
def foldFiberSingleCoordinateResidue (m k : ℕ) (x : foldFiberSingleCoordinateState m) :
    ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m) :=
  x.1 + if x.2 then foldFiberSingleCoordinateAffineDifferenceShift m k else 0

/-- The fiber profile counts all states with a fixed residue. -/
def foldFiberSingleCoordinateProfile (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) : Nat :=
  Fintype.card {x : foldFiberSingleCoordinateState m // foldFiberSingleCoordinateResidue m k x = r}

/-- The coordinate-1 count restricts the same fiber to states with the chosen bit equal to `1`. -/
def foldFiberSingleCoordinateOneCount (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) : Nat :=
  Fintype.card
    {x : foldFiberSingleCoordinateState m //
      x.2 = true ∧ foldFiberSingleCoordinateResidue m k x = r}

private noncomputable def foldFiberSingleCoordinateProfileEquivBool (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    {x : foldFiberSingleCoordinateState m // foldFiberSingleCoordinateResidue m k x = r} ≃ Bool where
  toFun x := x.1.2
  invFun b := ⟨(r - if b then foldFiberSingleCoordinateAffineDifferenceShift m k else 0, b), by
    simp [foldFiberSingleCoordinateResidue]⟩
  left_inv x := by
    rcases x with ⟨⟨s, b⟩, hx⟩
    have hs : s = r - if b then foldFiberSingleCoordinateAffineDifferenceShift m k else 0 := by
      simpa [foldFiberSingleCoordinateResidue] using eq_sub_of_add_eq hx
    apply Subtype.ext
    simp [hs]
  right_inv b := by
    simp

private theorem foldFiberSingleCoordinateProfile_eq_two (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateProfile m k r = 2 := by
  classical
  unfold foldFiberSingleCoordinateProfile
  simpa using Fintype.card_congr (foldFiberSingleCoordinateProfileEquivBool m k r)

private noncomputable def foldFiberSingleCoordinateOneCountEquivFinOne (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    {x : foldFiberSingleCoordinateState m //
      x.2 = true ∧ foldFiberSingleCoordinateResidue m k x = r} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨(r - foldFiberSingleCoordinateAffineDifferenceShift m k, true), by
    simp [foldFiberSingleCoordinateResidue]⟩
  left_inv x := by
    rcases x with ⟨⟨s, b⟩, hx⟩
    rcases hx with ⟨hb, hr⟩
    have hb' : b = true := by simpa using hb
    subst b
    have hs : s = r - foldFiberSingleCoordinateAffineDifferenceShift m k := by
      simpa [foldFiberSingleCoordinateResidue] using eq_sub_of_add_eq hr
    apply Subtype.ext
    simp [hs]
  right_inv i := by
    fin_cases i
    rfl

private theorem foldFiberSingleCoordinateOneCount_eq_one (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateOneCount m k r = 1 := by
  classical
  unfold foldFiberSingleCoordinateOneCount
  simpa using Fintype.card_congr (foldFiberSingleCoordinateOneCountEquivFinOne m k r)

/-- In the concrete single-coordinate model, every residue fiber contains exactly one state with the
chosen bit equal to `1` and one state with the chosen bit equal to `0`; equivalently, the bit-`1`
count at `r` together with the shifted bit-`1` count exhausts the full fiber profile.
    prop:fold-fiber-single-coordinate-affine-difference -/
theorem paper_fold_fiber_single_coordinate_affine_difference (m k : ℕ) :
    ∀ r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m),
      foldFiberSingleCoordinateOneCount m k r +
          foldFiberSingleCoordinateOneCount m k
            (r + foldFiberSingleCoordinateAffineDifferenceShift m k) =
        foldFiberSingleCoordinateProfile m k r := by
  intro r
  rw [foldFiberSingleCoordinateOneCount_eq_one, foldFiberSingleCoordinateOneCount_eq_one,
    foldFiberSingleCoordinateProfile_eq_two]

end Omega.Folding
