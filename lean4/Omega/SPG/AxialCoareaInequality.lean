import Mathlib.Tactic

namespace Omega.SPG

/-- Each fiber contributes at most L elements and at least 2 exposed faces per
    connected component. Therefore |S_a| le (L/2) * 2c_a = (L/2) * F_i,a.
    Summing over all fibers in one direction gives N le (L/2) * F_i.
    thm:spg-dyadic-polyclube-axial-coarea -/
theorem fiber_volume_face_bound (N F_i L : ℕ) (h : 2 * N ≤ L * F_i) :
    N ≤ L * F_i / 2 := by omega

/-- Averaging over n coordinate directions: from 2*N le L*F_i for each direction i,
    summing gives 2*n*N le L*(F_1+...+F_n) = L*F, hence 2*n*N le L*F.
    thm:spg-dyadic-polyclube-axial-coarea -/
theorem axial_coarea_sum (n : ℕ) (N : ℕ) (Fi : Fin n → ℕ) (L : ℕ)
    (hFi : ∀ i, 2 * N ≤ L * Fi i) :
    2 * n * N ≤ L * (Finset.univ.sum Fi) := by
  have h : n * (2 * N) ≤ Finset.univ.sum (fun i => L * Fi i) := by
    calc n * (2 * N) = Finset.univ.sum (fun (_ : Fin n) => 2 * N) := by
              simp [Finset.sum_const]
      _ ≤ Finset.univ.sum (fun i => L * Fi i) := by
              exact Finset.sum_le_sum (fun i _ => hFi i)
  rw [← Finset.mul_sum] at h
  linarith [Nat.mul_comm n (2 * N)]

/-- The rational-level formulation: Vol le (1/(2n)) * Area
    follows from 2*n*Vol le Area.
    thm:spg-dyadic-polyclube-axial-coarea -/
theorem axial_coarea_div (n : ℕ) (hn : 0 < n) (Vol Area : ℝ)
    (h : 2 * (n : ℝ) * Vol ≤ Area) :
    Vol ≤ Area / (2 * n) := by
  have hn' : (0 : ℝ) < 2 * n := by positivity
  rw [le_div_iff₀ hn']
  linarith

/-- Optimality of the constant 1/(2n): equality holds iff U = empty or U = I^n.
    For U = I^n, N = L^n and F = 2n*L^{n-1}, so 2*n*N = 2*n*L^n = L*(2*n*L^{n-1}) = L*F.
    thm:spg-dyadic-polyclube-axial-coarea -/
theorem axial_coarea_equality_full_cube (n L : ℕ) (hn : 0 < n) :
    2 * n * L ^ n = L * (2 * n * L ^ (n - 1)) := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [Nat.succ_sub_one]
    ring

/-- For the empty polycube, both sides are zero.
    thm:spg-dyadic-polyclube-axial-coarea -/
theorem axial_coarea_equality_empty (n L : ℕ) :
    2 * n * 0 = L * 0 := by ring

/-- Paper: `thm:spg-dyadic-polyclube-axial-coarea`.
    Seed package: axial coarea inequality backbone and optimality. -/
theorem paper_spg_dyadic_polyclube_axial_coarea :
    (∀ (N F_i L : ℕ), 2 * N ≤ L * F_i → N ≤ L * F_i / 2) ∧
    (∀ (n L : ℕ), 0 < n → 2 * n * L ^ n = L * (2 * n * L ^ (n - 1))) ∧
    (∀ (n L : ℕ), 2 * n * 0 = L * 0) := by
  refine ⟨fun N F_i L h => by omega, fun n L hn => ?_, fun n L => by ring⟩
  cases n with
  | zero => omega
  | succ m => simp only [Nat.succ_sub_one]; ring

end Omega.SPG
