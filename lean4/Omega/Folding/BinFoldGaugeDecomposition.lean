import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Folding

/-- The finite input cube for the length-`m` BinFold map. -/
abbrev BinFoldInput (m : ℕ) := Fin (2 ^ m)

/-- The concrete finite fiber of `cBinFold` over `x`. -/
def cBinFoldFiber (m : ℕ) (x : Omega.X m) :=
  {n : BinFoldInput m // Omega.cBinFold m n.1 = x}

/-- The gauge group of `cBinFold`: permutations of the finite input cube that preserve the
BinFold fiber projection. -/
def BinFoldGauge (m : ℕ) :=
  {σ : Equiv.Perm (BinFoldInput m) //
    ∀ n : BinFoldInput m, Omega.cBinFold m (σ n).1 = Omega.cBinFold m n.1}

/-- A fiber-preserving permutation restricts to a permutation of every BinFold fiber. -/
noncomputable def restrictGauge {m : ℕ} (σ : BinFoldGauge m) (x : Omega.X m) :
    Equiv.Perm (cBinFoldFiber m x) where
  toFun a :=
    ⟨σ.1 a.1, by
      simpa [a.2] using σ.2 a.1⟩
  invFun a :=
    ⟨σ.1.symm a.1, by
      have hpres := σ.2 (σ.1.symm a.1)
      have hstep : Omega.cBinFold m (σ.1.symm a.1).1 = Omega.cBinFold m a.1.1 := by
        simpa using hpres.symm
      exact hstep.trans a.2⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

/-- The finite input cube is the disjoint sigma-union of the BinFold fibers. -/
noncomputable def binFoldInputFiberEquiv (m : ℕ) :
    BinFoldInput m ≃ Σ x : Omega.X m, cBinFoldFiber m x where
  toFun n := ⟨Omega.cBinFold m n.1, ⟨n, rfl⟩⟩
  invFun a := a.2.1
  left_inv n := rfl
  right_inv a := by
    rcases a with ⟨x, ⟨n, hn⟩⟩
    cases hn
    rfl

/-- Assemble a global fiber-preserving permutation from a family of fiberwise permutations on the
disjoint fiber partition. -/
noncomputable def assembleGauge {m : ℕ}
    (ρ : (x : Omega.X m) → Equiv.Perm (cBinFoldFiber m x)) : BinFoldGauge m where
  val :=
    (binFoldInputFiberEquiv m).trans ((Equiv.sigmaCongrRight ρ).trans (binFoldInputFiberEquiv m).symm)
  property := by
    intro n
    change ((binFoldInputFiberEquiv m)
        ((binFoldInputFiberEquiv m).symm
          ((Equiv.sigmaCongrRight ρ) ((binFoldInputFiberEquiv m) n)))).1
      = ((binFoldInputFiberEquiv m) n).1
    simp

/-- Decomposition of a gauge permutation into its family of restricted fiberwise permutations. -/
noncomputable def decomposeGauge (m : ℕ) :
    BinFoldGauge m → (x : Omega.X m) → Equiv.Perm (cBinFoldFiber m x) :=
  fun σ x => restrictGauge σ x

theorem assembleGauge_leftInverse (m : ℕ) :
    Function.LeftInverse (@assembleGauge m) (decomposeGauge m) := by
  intro σ
  apply Subtype.ext
  ext n
  rfl

theorem assembleGauge_rightInverse (m : ℕ) :
    Function.RightInverse (@assembleGauge m) (decomposeGauge m) := by
  intro ρ
  funext x
  ext a
  rcases a with ⟨n, hn⟩
  apply Subtype.ext
  cases hn
  rfl

theorem decomposeGauge_bijective (m : ℕ) :
    Function.Bijective (decomposeGauge m) := by
  exact ⟨(assembleGauge_leftInverse m).injective, (assembleGauge_rightInverse m).surjective⟩

/-- Paper-facing gauge decomposition for BinFold: fiber-preserving permutations restrict to
permutations of each fiber, and conversely a family of fiberwise permutations assembles to a
unique global gauge permutation via the disjoint fiber partition.
    prop:fold-bin-gauge-decomposition -/
def paper_fold_bin_gauge_decomposition (m : ℕ) : Prop := by
  exact
    Function.Bijective (decomposeGauge m) ∧
      Function.LeftInverse (@assembleGauge m) (decomposeGauge m) ∧
      Function.RightInverse (@assembleGauge m) (decomposeGauge m)

theorem paper_fold_bin_gauge_decomposition_spec (m : ℕ) :
    paper_fold_bin_gauge_decomposition m := by
  exact ⟨decomposeGauge_bijective m, assembleGauge_leftInverse m, assembleGauge_rightInverse m⟩

end Omega.Folding
