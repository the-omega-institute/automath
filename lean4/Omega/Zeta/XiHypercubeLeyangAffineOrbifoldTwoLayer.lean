import Mathlib.Tactic
import Omega.Core.WalshFourier
import Omega.Zeta.WalshParseval

namespace Omega.Zeta

open Omega.Core Finset

private def xiCoord0 : Fin 2 := ⟨0, by decide⟩
private def xiCoord1 : Fin 2 := ⟨1, by decide⟩

private def xiSingleton0 : Finset (Fin 2) := {xiCoord0}
private def xiSingleton1 : Finset (Fin 2) := {xiCoord1}
private def xiPair : Finset (Fin 2) := {xiCoord0, xiCoord1}

/-- The affine involution `σ(y₀,y₁) = (1 - y₁, 1 - y₀)` on the two-cube. -/
def xiAffineSwapInvolution (w : Word 2) : Word 2 :=
  fun r => if r = xiCoord0 then !(w xiCoord1) else !(w xiCoord0)

@[simp] lemma xiAffineSwapInvolution_zero (w : Word 2) :
    xiAffineSwapInvolution w xiCoord0 = !(w xiCoord1) := by
  simp [xiAffineSwapInvolution, xiCoord0]

@[simp] lemma xiAffineSwapInvolution_one (w : Word 2) :
    xiAffineSwapInvolution w xiCoord1 = !(w xiCoord0) := by
  simp [xiAffineSwapInvolution, xiCoord1, xiCoord0]

@[simp] lemma xiAffineSwapInvolution_involutive (w : Word 2) :
    xiAffineSwapInvolution (xiAffineSwapInvolution w) = w := by
  funext r
  fin_cases r <;> simp [xiAffineSwapInvolution, xiCoord0, xiCoord1]

private lemma word2_cases (w : Word 2) :
    ∃ b0 b1 : Bool, w = fun i => if i = (0 : Fin 2) then b0 else b1 := by
  refine ⟨w 0, w 1, ?_⟩
  funext i
  fin_cases i <;> simp

lemma xi_singleton0_transforms (w : Word 2) :
    walshChar xiSingleton0 (xiAffineSwapInvolution w) = -walshChar xiSingleton1 w := by
  rcases word2_cases w with ⟨b0, b1, rfl⟩
  cases b0 <;> cases b1 <;>
  native_decide

lemma xi_singleton1_transforms (w : Word 2) :
    walshChar xiSingleton1 (xiAffineSwapInvolution w) = -walshChar xiSingleton0 w := by
  rcases word2_cases w with ⟨b0, b1, rfl⟩
  cases b0 <;> cases b1 <;>
  native_decide

lemma xi_pair_transforms (w : Word 2) :
    walshChar xiPair (xiAffineSwapInvolution w) = walshChar xiPair w := by
  rcases word2_cases w with ⟨b0, b1, rfl⟩
  cases b0 <;> cases b1 <;>
  native_decide

lemma xiWalshBias_singleton_antisymmetry (f : Word 2 → ℤ)
    (hf : ∀ y, f (xiAffineSwapInvolution y) = f y) :
    walshBias f xiSingleton0 = -walshBias f xiSingleton1 := by
  let e : Word 2 ≃ Word 2 :=
    { toFun := xiAffineSwapInvolution
      invFun := xiAffineSwapInvolution
      left_inv := xiAffineSwapInvolution_involutive
      right_inv := xiAffineSwapInvolution_involutive }
  have hsum :
      walshBias f xiSingleton0 =
        ∑ y : Word 2,
          walshChar xiSingleton0 (xiAffineSwapInvolution y) * f (xiAffineSwapInvolution y) := by
    unfold walshBias
    exact Fintype.sum_equiv e
      (fun w : Word 2 => walshChar xiSingleton0 w * f w)
      (fun y : Word 2 =>
        walshChar xiSingleton0 (xiAffineSwapInvolution y) * f (xiAffineSwapInvolution y))
      (by intro y; simp [e, xiAffineSwapInvolution_involutive])
  calc
    walshBias f xiSingleton0
      = ∑ y : Word 2,
          walshChar xiSingleton0 (xiAffineSwapInvolution y) * f (xiAffineSwapInvolution y) := hsum
    _ = ∑ y : Word 2, (-walshChar xiSingleton1 y) * f y := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [hf y, xi_singleton0_transforms]
    _ = -∑ y : Word 2, walshChar xiSingleton1 y * f y := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro y hy
          ring
    _ = -walshBias f xiSingleton1 := by
          rfl

lemma xi_character_difference_factorization (x : Word 2) :
    walshChar xiSingleton0 x - walshChar xiSingleton1 x =
      -(1 - walshChar xiPair x) * walshChar xiSingleton1 x := by
  rcases word2_cases x with ⟨b0, b1, rfl⟩
  cases b0 <;> cases b1 <;>
  native_decide

lemma xi_pair_char_of_eq (x : Word 2) (h : x xiCoord0 = x xiCoord1) :
    walshChar xiPair x = 1 := by
  rcases word2_cases x with ⟨b0, b1, rfl⟩
  cases b0 <;> cases b1 <;> simp [xiCoord0, xiCoord1] at h ⊢ <;> native_decide

lemma xi_pair_char_of_ne (x : Word 2) (h : x xiCoord0 ≠ x xiCoord1) :
    walshChar xiPair x = -1 := by
  rcases word2_cases x with ⟨b0, b1, rfl⟩
  cases b0 <;> cases b1 <;> simp [xiCoord0, xiCoord1] at h ⊢ <;> native_decide

/-- Concrete two-layer decomposition on the two-cube under the affine involution.
This is the `k = 2` Lee-Yang/Walsh model of the paper's even/odd splitting. -/
def xiHypercubeLeyangAffineOrbifoldTwoLayerStatement : Prop :=
  ∀ f : Word 2 → ℤ, (∀ y, f (xiAffineSwapInvolution y) = f y) →
    ∀ x : Word 2,
      let pEven := walshBias f ∅ + walshBias f xiPair * walshChar xiPair x
      let qOdd := -walshBias f xiSingleton0 * walshChar xiSingleton1 x
      (walshBias f ∅ +
          walshBias f xiSingleton0 * walshChar xiSingleton0 x +
          walshBias f xiSingleton1 * walshChar xiSingleton1 x +
          walshBias f xiPair * walshChar xiPair x =
        pEven + (1 - walshChar xiPair x) * qOdd) ∧
      ((x xiCoord0 = x xiCoord1) →
        walshBias f ∅ +
            walshBias f xiSingleton0 * walshChar xiSingleton0 x +
            walshBias f xiSingleton1 * walshChar xiSingleton1 x +
            walshBias f xiPair * walshChar xiPair x = pEven) ∧
      ((x xiCoord0 ≠ x xiCoord1) →
        walshBias f ∅ +
            walshBias f xiSingleton0 * walshChar xiSingleton0 x +
            walshBias f xiSingleton1 * walshChar xiSingleton1 x +
            walshBias f xiPair * walshChar xiPair x = pEven + 2 * qOdd)

theorem xiHypercubeLeyangAffineOrbifoldTwoLayerStatement_true :
    xiHypercubeLeyangAffineOrbifoldTwoLayerStatement := by
  intro f hf x
  dsimp [xiHypercubeLeyangAffineOrbifoldTwoLayerStatement]
  have hanti : walshBias f xiSingleton1 = -walshBias f xiSingleton0 := by
    have h := xiWalshBias_singleton_antisymmetry f hf
    linarith
  have hodd :
      walshBias f xiSingleton0 * walshChar xiSingleton0 x +
          walshBias f xiSingleton1 * walshChar xiSingleton1 x =
        (1 - walshChar xiPair x) *
          (-walshBias f xiSingleton0 * walshChar xiSingleton1 x) := by
    rw [hanti]
    calc
      walshBias f xiSingleton0 * walshChar xiSingleton0 x +
          (-walshBias f xiSingleton0) * walshChar xiSingleton1 x
        = walshBias f xiSingleton0 *
            (walshChar xiSingleton0 x - walshChar xiSingleton1 x) := by
              ring
      _ = walshBias f xiSingleton0 *
            (-(1 - walshChar xiPair x) * walshChar xiSingleton1 x) := by
              rw [xi_character_difference_factorization]
      _ = (1 - walshChar xiPair x) *
            (-walshBias f xiSingleton0 * walshChar xiSingleton1 x) := by
              ring
  let pEven := walshBias f ∅ + walshBias f xiPair * walshChar xiPair x
  let qOdd := -walshBias f xiSingleton0 * walshChar xiSingleton1 x
  have hmain :
      walshBias f ∅ +
          walshBias f xiSingleton0 * walshChar xiSingleton0 x +
          walshBias f xiSingleton1 * walshChar xiSingleton1 x +
          walshBias f xiPair * walshChar xiPair x =
        pEven + (1 - walshChar xiPair x) * qOdd := by
    dsimp [pEven, qOdd]
    linarith [hodd]
  refine ⟨?_, ?_, ?_⟩
  · simpa [pEven, qOdd] using hmain
  · intro hx
    have hpair : walshChar xiPair x = 1 := xi_pair_char_of_eq x hx
    rw [hpair] at hmain
    simpa [pEven, qOdd, hpair] using hmain
  · intro hx
    have hpair : walshChar xiPair x = -1 := xi_pair_char_of_ne x hx
    rw [hpair] at hmain
    simpa [pEven, qOdd, hpair] using hmain

/-- Paper label: `thm:xi-hypercube-leyang-affine-orbifold-two-layer`.
The requested paper-facing name is the concrete proposition proved by the two-cube Walsh package
above. -/
def paper_xi_hypercube_leyang_affine_orbifold_two_layer : Prop :=
  xiHypercubeLeyangAffineOrbifoldTwoLayerStatement

theorem paper_xi_hypercube_leyang_affine_orbifold_two_layer_verified :
    paper_xi_hypercube_leyang_affine_orbifold_two_layer :=
  xiHypercubeLeyangAffineOrbifoldTwoLayerStatement_true

end Omega.Zeta
