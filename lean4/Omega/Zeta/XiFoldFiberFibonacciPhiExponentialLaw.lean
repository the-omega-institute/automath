import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-fiber-fibonacci-phi-exponential-law`. -/
theorem paper_xi_fold_fiber_fibonacci_phi_exponential_law (phi : ℝ) (lengths : List ℕ)
    (fiberCard diam r : ℕ) (hphi : 1 < phi)
    (hFiber : fiberCard = (lengths.map (fun l => Nat.fib (l + 2))).prod)
    (hDiam : diam = lengths.sum) (hr : r = lengths.length)
    (hLower : ∀ l ∈ lengths, phi ^ l ≤ (Nat.fib (l + 2) : ℝ))
    (hUpper : ∀ l ∈ lengths, (Nat.fib (l + 2) : ℝ) ≤ phi ^ (l + 1)) :
    phi ^ diam ≤ (fiberCard : ℝ) ∧ (fiberCard : ℝ) ≤ phi ^ (diam + r) := by
  have hphi_nonneg : 0 ≤ phi := le_of_lt (lt_trans zero_lt_one hphi)
  have hFiberReal :
      (fiberCard : ℝ) = ((lengths.map (fun l => Nat.fib (l + 2))).prod : ℝ) := by
    exact_mod_cast hFiber
  have hLowerProdAll :
      ∀ L : List ℕ, (∀ l ∈ L, phi ^ l ≤ (Nat.fib (l + 2) : ℝ)) →
        phi ^ L.sum ≤ ((L.map (fun l => Nat.fib (l + 2))).prod : ℝ) := by
    intro L hL
    induction L with
    | nil =>
        simp
    | cons l L ih =>
        have hhead : phi ^ l ≤ (Nat.fib (l + 2) : ℝ) := hL l (by simp)
        have htail :
            phi ^ L.sum ≤ ((L.map (fun l => Nat.fib (l + 2))).prod : ℝ) := by
          exact ih (fun m hm => hL m (by simp [hm]))
        calc
          phi ^ (List.sum (l :: L)) = phi ^ l * phi ^ L.sum := by
            simp [pow_add]
          _ ≤ (Nat.fib (l + 2) : ℝ) *
              ((L.map (fun l => Nat.fib (l + 2))).prod : ℝ) := by
            exact mul_le_mul hhead htail (pow_nonneg hphi_nonneg _) (by positivity)
          _ = (((l :: L).map (fun l => Nat.fib (l + 2))).prod : ℝ) := by
            simp
  have hLowerProd :
      phi ^ lengths.sum ≤ ((lengths.map (fun l => Nat.fib (l + 2))).prod : ℝ) :=
    hLowerProdAll lengths hLower
  have hUpperProdAll :
      ∀ L : List ℕ, (∀ l ∈ L, (Nat.fib (l + 2) : ℝ) ≤ phi ^ (l + 1)) →
        ((L.map (fun l => Nat.fib (l + 2))).prod : ℝ) ≤ phi ^ (L.sum + L.length) := by
    intro L hL
    induction L with
    | nil =>
        simp
    | cons l L ih =>
        have hhead : (Nat.fib (l + 2) : ℝ) ≤ phi ^ (l + 1) := hL l (by simp)
        have htail :
            ((L.map (fun l => Nat.fib (l + 2))).prod : ℝ) ≤
              phi ^ (L.sum + L.length) := by
          exact ih (fun m hm => hL m (by simp [hm]))
        calc
          (((l :: L).map (fun l => Nat.fib (l + 2))).prod : ℝ) =
              (Nat.fib (l + 2) : ℝ) *
                ((L.map (fun l => Nat.fib (l + 2))).prod : ℝ) := by
            simp
          _ ≤ phi ^ (l + 1) * phi ^ (L.sum + L.length) := by
            exact mul_le_mul hhead htail (by positivity) (pow_nonneg hphi_nonneg _)
          _ = phi ^ (List.sum (l :: L) + List.length (l :: L)) := by
            rw [← pow_add]
            congr 1
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hUpperProd :
      ((lengths.map (fun l => Nat.fib (l + 2))).prod : ℝ) ≤
        phi ^ (lengths.sum + lengths.length) :=
    hUpperProdAll lengths hUpper
  constructor
  · rw [hDiam, hFiberReal]
    exact hLowerProd
  · rw [hDiam, hr, hFiberReal]
    exact hUpperProd

end Omega.Zeta
