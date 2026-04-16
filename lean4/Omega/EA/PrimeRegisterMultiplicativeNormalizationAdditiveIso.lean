import Mathlib.Data.Nat.Fib.Zeckendorf
import Omega.EA.InternalProductAddsValues
import Omega.EA.PrimeRegisterFibValuation
import Omega.Folding.Fold
import Omega.Folding.Rewrite

namespace Omega.EA

abbrev DigitCfg := Omega.Rewrite.DigitCfg

local instance : IsTrans Nat (fun a b ↦ b + 2 ≤ a) where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- The canonical prime register attached to a Zeckendorf index list. -/
noncomputable def registerOfIndices : List Nat → DigitCfg
  | [] => (0 : DigitCfg)
  | k :: ks => Finsupp.single (k - 2) 1 + registerOfIndices ks

private theorem isZeckendorfRep_tail :
    ∀ {a : Nat} {l : List Nat}, (a :: l).IsZeckendorfRep → l.IsZeckendorfRep
  | a, l, h => by
      have hChain : List.IsChain (fun a b : Nat ↦ b + 2 ≤ a) (a :: (l ++ [0])) := by
        simpa [List.IsZeckendorfRep, List.cons_append] using h
      simpa [List.IsZeckendorfRep] using hChain.tail

private theorem two_le_of_mem_isZeckendorfRep :
    ∀ {l : List Nat} {a : Nat}, l.IsZeckendorfRep → a ∈ l → 2 ≤ a
  | [], _a, _hRep, hMem => by
      cases hMem
  | b :: l, a, hRep, hMem => by
      have hChain : List.IsChain (fun a b : Nat ↦ b + 2 ≤ a) (b :: (l ++ [0])) := by
        simpa [List.IsZeckendorfRep, List.cons_append] using hRep
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · have hRel : 0 + 2 ≤ a := hChain.rel_cons (List.mem_append_right l (by simp))
        simpa using hRel
      · exact two_le_of_mem_isZeckendorfRep (isZeckendorfRep_tail hRep) hMem

private theorem valPr_registerOfIndices :
    ∀ {l : List Nat}, l.IsZeckendorfRep →
      valPr (registerOfIndices l) = (l.map Nat.fib).sum
  | [], _ => by
      simpa using (valPr_zero)
  | k :: ks, hRep => by
      have hk : 2 ≤ k := two_le_of_mem_isZeckendorfRep hRep (by simp)
      have hTail : ks.IsZeckendorfRep := isZeckendorfRep_tail hRep
      calc
        valPr (registerOfIndices (k :: ks))
            = valPr (Finsupp.single (k - 2) 1 + registerOfIndices ks) := rfl
        _ = valPr (Finsupp.single (k - 2) 1) + valPr (registerOfIndices ks) := by
              rw [valPr_add]
        _ = Nat.fib k + (ks.map Nat.fib).sum := by
              rw [valPr_single, valPr_registerOfIndices hTail, Nat.sub_add_cancel hk]
              norm_num
        _ = ((k :: ks).map Nat.fib).sum := by simp

/-- The paper-facing Fibonacci register representative `R_F(n)`. -/
noncomputable def R_F (n : ℕ) : DigitCfg :=
  registerOfIndices (Nat.zeckendorf n)

@[simp] theorem valPr_R_F (n : ℕ) : valPr (R_F n) = n := by
  calc
    valPr (R_F n) = ((Nat.zeckendorf n).map Nat.fib).sum := by
      simpa [R_F] using valPr_registerOfIndices (Nat.isZeckendorfRep_zeckendorf n)
    _ = n := Omega.sum_nat_zeckendorf_fib n

/-- Register multiplication is multiplication of monomials, hence addition of exponent vectors. -/
noncomputable def primeRegisterMul (a b : DigitCfg) : DigitCfg :=
  a + b

/-- Paper normal form: rewrite by valuation and then return the canonical `R_F` representative. -/
noncomputable def NF_pr (a : DigitCfg) : DigitCfg :=
  R_F (valPr a)

/-- The normalized prime-register image. -/
def PrimeRegister :=
  Set.range R_F

/-- The canonical inclusion `ℕ → ZG = R_F(ℕ)`. -/
noncomputable def primeRegisterLift (n : ℕ) : PrimeRegister :=
  ⟨R_F n, ⟨n, rfl⟩⟩

/-- The internalized additive law on prime registers. -/
noncomputable def boxplus_pr (x y : PrimeRegister) : PrimeRegister :=
  ⟨NF_pr (primeRegisterMul x.1 y.1), ⟨valPr (primeRegisterMul x.1 y.1), rfl⟩⟩

private theorem primeRegisterLift_injective : Function.Injective primeRegisterLift := by
  intro m n h
  have hcfg : R_F m = R_F n := congrArg (fun x : PrimeRegister => x.1) h
  have hval : valPr (R_F m) = valPr (R_F n) := congrArg valPr hcfg
  simpa using hval

private theorem primeRegisterLift_surjective : Function.Surjective primeRegisterLift := by
  intro x
  rcases x.2 with ⟨n, hn⟩
  exact ⟨n, Subtype.ext hn⟩

private theorem valPr_primeRegisterMul (m n : ℕ) :
    valPr (primeRegisterMul (R_F m) (R_F n)) = m + n := by
  have hadd :=
    (Omega.EA.InternalProductAddsValues.paper_prime_register_internal_product_adds_values).1
      (R_F m) (R_F n)
  simpa [primeRegisterMul, valPr_R_F] using hadd

private theorem NF_pr_primeRegisterMul (m n : ℕ) :
    NF_pr (primeRegisterMul (R_F m) (R_F n)) = R_F (m + n) := by
  simp [NF_pr, valPr_primeRegisterMul]

/-- Paper-facing wrapper: multiplication followed by normalization is exactly addition on values,
    and the canonical register map identifies `ℕ` with the normalized prime-register monoid. -/
theorem paper_prime_register_multiplicative_normalization_additive_iso :
    (∀ m n : ℕ, valPr (primeRegisterMul (R_F m) (R_F n)) = m + n) ∧
    (∀ m n : ℕ, NF_pr (primeRegisterMul (R_F m) (R_F n)) = R_F (m + n)) ∧
    (∀ m n : ℕ, boxplus_pr (primeRegisterLift m) (primeRegisterLift n) =
      primeRegisterLift (m + n)) ∧
    Function.Bijective primeRegisterLift := by
  refine ⟨?_, ?_, ?_, ⟨primeRegisterLift_injective, primeRegisterLift_surjective⟩⟩
  · exact valPr_primeRegisterMul
  · exact NF_pr_primeRegisterMul
  · intro m n
    apply Subtype.ext
    exact NF_pr_primeRegisterMul m n

end Omega.EA
