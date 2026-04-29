import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.POM.PrimeDeterminant2x2FreeEncoding
import Omega.POM.PrimeDeterminantEllipseLedger

namespace Omega.POM

open Matrix

/-- The Parikh vector of a word over `Fin k`. -/
def parikhVector {k : ℕ} (w : List (Fin k)) : Fin k → Nat := fun i => w.count i

/-- The determinant predicted by the Parikh vector. -/
def parikhPrimeProduct {k : ℕ} (p : Fin k → ℕ) (w : List (Fin k)) : ℕ :=
  ∏ i : Fin k, p i ^ parikhVector w i

/-- The ellipse-area package only remembers the determinant factor, up to multiplication by `π`.
-/
noncomputable def primeDetArea {k : ℕ} (p : Fin k → ℕ) (w : List (Fin k)) : ℝ :=
  Real.pi * (parikhPrimeProduct p w : ℝ)

/-- The paper-facing determinant/Parikh package: the determinant factors through the Parikh vector;
when the prime labelling is injective, equality of determinants and equality of areas both reduce
to equality of Parikh vectors.
    thm:pom-prime-determinant-abelianization-factorization -/
def PrimeDeterminantAbelianizationFactorization {k N : ℕ} (p : Fin k → ℕ)
    (_hprime : ∀ i, Nat.Prime (p i)) (_hN : 1 ≤ N) (_hbound : ∀ i, p i < N) : Prop :=
  (∀ w,
      ((primeDetWordMatrix N p w).map Int.ofNatHom).det =
        ∏ i : Fin k, (p i : ℤ) ^ parikhVector w i) ∧
    (Function.Injective p →
      ∀ u v,
        ((primeDetWordMatrix N p u).map Int.ofNatHom).det =
            ((primeDetWordMatrix N p v).map Int.ofNatHom).det ↔
          parikhVector u = parikhVector v) ∧
    (Function.Injective p →
      ∀ u v, primeDetArea p u = primeDetArea p v ↔ parikhVector u = parikhVector v)

lemma parikhProduct_eq_list_prod {k : ℕ} {α : Type*} [CommMonoid α] (f : Fin k → α)
    (w : List (Fin k)) :
    (∏ i : Fin k, f i ^ parikhVector w i) = (w.map f).prod := by
  classical
  calc
    ∏ i : Fin k, f i ^ parikhVector w i
        = Finset.prod w.toFinset (fun i => f i ^ w.count i) := by
            symm
            refine Finset.prod_subset (by intro i _; simp) ?_
            intro i _ hi
            have hi' : i ∉ w.toFinset := hi
            simp [parikhVector, List.count_eq_zero_of_not_mem (mt List.mem_toFinset.2 hi')]
    _ = (w.map f).prod := by
      symm
      exact Finset.prod_list_map_count w f

lemma parikhPrimeProduct_eq_list_prod {k : ℕ} (p : Fin k → ℕ) (w : List (Fin k)) :
    parikhPrimeProduct p w = (w.map p).prod := by
  simpa [parikhPrimeProduct] using parikhProduct_eq_list_prod p w

lemma map_natCast_comp_eq_map_int {k : ℕ} (p : Fin k → ℕ) (w : List (Fin k)) :
    (w.map (Nat.cast ∘ p) : List ℤ) = w.map (fun i => (p i : ℤ)) := by
  induction w with
  | nil =>
      rfl
  | cons i w ih =>
      simp [ih, Function.comp]

lemma map_natCast_map_eq_map_int {k : ℕ} (p : Fin k → ℕ) (w : List (Fin k)) :
    (List.map Nat.cast (List.map p w) : List ℤ) = w.map (fun i => (p i : ℤ)) := by
  induction w with
  | nil =>
      rfl
  | cons i w ih =>
      simp [ih]

lemma primeDetWordMatrix_det_list_formula {k N : ℕ} (p : Fin k → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hN : 1 ≤ N) (hbound : ∀ i, p i < N) (w : List (Fin k)) :
    ((primeDetWordMatrix N p w).map Int.ofNatHom).det = (w.map fun i => (p i : ℤ)).prod := by
  have hgen := (paper_pom_prime_determinant_2x2_free_encoding p hprime hN hbound).1
  induction w with
  | nil =>
      simp [primeDetWordMatrix]
  | cons i w ih =>
      calc
        ((primeDetWordMatrix N p (i :: w)).map Int.ofNatHom).det
            = ((primeDetGenMatrix N p i).map Int.ofNatHom).det *
                ((primeDetWordMatrix N p w).map Int.ofNatHom).det := by
                  simp [primeDetWordMatrix, Matrix.det_mul]
        _ = (p i : ℤ) * (w.map fun j => (p j : ℤ)).prod := by rw [hgen i, ih]
        _ = ((i :: w).map fun j => (p j : ℤ)).prod := by simp

lemma primeDetWordMatrix_det_formula {k N : ℕ} (p : Fin k → ℕ) (hprime : ∀ i, Nat.Prime (p i))
    (hN : 1 ≤ N) (hbound : ∀ i, p i < N) (w : List (Fin k)) :
    ((primeDetWordMatrix N p w).map Int.ofNatHom).det =
      ∏ i : Fin k, (p i : ℤ) ^ parikhVector w i := by
  rw [primeDetWordMatrix_det_list_formula p hprime hN hbound]
  symm
  exact parikhProduct_eq_list_prod (fun i => (p i : ℤ)) w

lemma parikhPrimeProduct_factorization {k : ℕ} (p : Fin k → ℕ) (hprime : ∀ i, Nat.Prime (p i))
    (hpinj : Function.Injective p) (w : List (Fin k)) (i : Fin k) :
    (parikhPrimeProduct p w).factorization (p i) = parikhVector w i := by
  classical
  unfold parikhPrimeProduct parikhVector
  rw [Nat.factorization_prod_apply]
  · simp_rw [Nat.factorization_pow, Finsupp.smul_apply]
    have hfac : ∀ j : Fin k, (p j).factorization (p i) = if j = i then 1 else 0 := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp [Nat.Prime.factorization_self (hprime j)]
      · have hneq : p j ≠ p i := by
          exact fun hEq => hji (hpinj hEq)
        simpa [hji, hneq] using congrArg (fun f => f (p i)) (Nat.Prime.factorization (hprime j))
    simp [hfac]
  · intro j _
    exact pow_ne_zero _ (hprime j).ne_zero

lemma parikhPrimeProduct_eq_iff {k : ℕ} (p : Fin k → ℕ) (hprime : ∀ i, Nat.Prime (p i))
    (hpinj : Function.Injective p) (u v : List (Fin k)) :
    parikhPrimeProduct p u = parikhPrimeProduct p v ↔ parikhVector u = parikhVector v := by
  constructor
  · intro hprod
    funext i
    have hfac := congrArg (fun n : ℕ => n.factorization (p i)) hprod
    simpa [parikhPrimeProduct_factorization p hprime hpinj u i,
      parikhPrimeProduct_factorization p hprime hpinj v i] using hfac
  · intro hparikh
    simpa [parikhPrimeProduct, hparikh]

/-- Paper label:
`thm:pom-prime-determinant-abelianization-factorization`. -/
theorem paper_pom_prime_determinant_abelianization_factorization {k N : ℕ} (p : Fin k → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hN : 1 ≤ N) (hbound : ∀ i, p i < N) :
    PrimeDeterminantAbelianizationFactorization p hprime hN hbound := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact primeDetWordMatrix_det_formula p hprime hN hbound w
  · intro hpinj u v
    constructor
    · intro hdet
      have hdet' :
          (u.map fun i => (p i : ℤ)).prod = (v.map fun i => (p i : ℤ)).prod := by
        calc
          (u.map fun i => (p i : ℤ)).prod
              = ((primeDetWordMatrix N p u).map Int.ofNatHom).det := by
                  symm
                  exact primeDetWordMatrix_det_list_formula p hprime hN hbound u
          _ = ((primeDetWordMatrix N p v).map Int.ofNatHom).det := hdet
          _ = (v.map fun i => (p i : ℤ)).prod :=
                primeDetWordMatrix_det_list_formula p hprime hN hbound v
      have hlist :
          (u.map p).prod = (v.map p).prod := by
        have hlist_cast : ((u.map p).prod : ℤ) = (v.map p).prod := by
          calc
            ((u.map p).prod : ℤ) = (u.map fun i => (p i : ℤ)).prod := by
              rw [Nat.cast_list_prod]
              rw [map_natCast_map_eq_map_int p u]
            _ = (v.map fun i => (p i : ℤ)).prod := hdet'
            _ = ((v.map p).prod : ℤ) := by
              symm
              rw [Nat.cast_list_prod]
              rw [map_natCast_map_eq_map_int p v]
        exact_mod_cast hlist_cast
      rw [← parikhPrimeProduct_eq_list_prod p u, ← parikhPrimeProduct_eq_list_prod p v] at hlist
      exact (parikhPrimeProduct_eq_iff p hprime hpinj u v).mp hlist
    · intro hparikh
      rw [primeDetWordMatrix_det_formula p hprime hN hbound,
        primeDetWordMatrix_det_formula p hprime hN hbound, hparikh]
  · intro hpinj u v
    constructor
    · intro harea
      have hprod_real : (parikhPrimeProduct p u : ℝ) = parikhPrimeProduct p v := by
        exact mul_left_cancel₀ Real.pi_ne_zero (by simpa [primeDetArea] using harea)
      have hprod_nat : parikhPrimeProduct p u = parikhPrimeProduct p v := by
        exact_mod_cast hprod_real
      exact (parikhPrimeProduct_eq_iff p hprime hpinj u v).mp hprod_nat
    · intro hparikh
      have hprod : parikhPrimeProduct p u = parikhPrimeProduct p v := by
        simpa [parikhPrimeProduct, hparikh]
      rw [primeDetArea, primeDetArea, hprod]

end Omega.POM
