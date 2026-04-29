import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

namespace Omega.Zeta

/-- The affine-tail defect `G(t)=Λ(t)-(α*t+g)` for the part 57f convex extension. -/
def xi_time_part57f_convex_extension_affine_tail_defect
    (Λ : ℝ → ℝ) (alphaStar gStar t : ℝ) : ℝ :=
  Λ t - (alphaStar * t + gStar)

/-- On a unit interval, nonnegative convex defect with zero integer endpoints is identically zero. -/
theorem xi_time_part57f_convex_extension_affine_tail_unit_interval
    (Λ : ℝ → ℝ) (alphaStar gStar : ℝ) (a0 n : ℕ)
    (hconv :
      ConvexOn ℝ (Set.Ici (a0 : ℝ))
        (fun t => xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar t))
    (hnonneg :
      ∀ t : ℝ, (a0 : ℝ) ≤ t →
        0 ≤ xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar t)
    (hzero :
      ∀ m : ℕ, a0 ≤ m →
        xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar (m : ℝ) = 0)
    (hn : a0 ≤ n) :
    ∀ t ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ), Λ t = alphaStar * t + gStar := by
  intro t ht
  let G : ℝ → ℝ := fun t =>
    xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar t
  have hn_mem : (n : ℝ) ∈ Set.Ici (a0 : ℝ) := by
    show (a0 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hn1_mem : ((n + 1 : ℕ) : ℝ) ∈ Set.Ici (a0 : ℝ) := by
    show (a0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast (Nat.le_trans hn (Nat.le_succ n))
  have hleft_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) - t := by
    linarith [ht.2]
  have hright_nonneg : 0 ≤ t - (n : ℝ) := by
    linarith [ht.1]
  have hsum : (((n + 1 : ℕ) : ℝ) - t) + (t - (n : ℝ)) = 1 := by
    norm_num
  have hconvex :=
    hconv.2 hn_mem hn1_mem hleft_nonneg hright_nonneg hsum
  have hpoint :
      ((((n + 1 : ℕ) : ℝ) - t) • (n : ℝ) +
          (t - (n : ℝ)) • (((n + 1 : ℕ) : ℝ))) = t := by
    simp [smul_eq_mul]
    ring
  have hupper : G t ≤ 0 := by
    rw [hpoint] at hconvex
    have hzero_n : G (n : ℝ) = 0 := by
      simpa [G] using hzero n hn
    have hzero_n1 : G ((n : ℝ) + 1) = 0 := by
      simpa [G, Nat.cast_add, Nat.cast_one] using
        hzero (n + 1) (Nat.le_trans hn (Nat.le_succ n))
    simpa [G, hzero_n, hzero_n1, smul_eq_mul] using hconvex
  have hlower : 0 ≤ G t := hnonneg t (le_trans (by exact_mod_cast hn) ht.1)
  have hG : G t = 0 := le_antisymm hupper hlower
  change xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar t = 0 at hG
  unfold xi_time_part57f_convex_extension_affine_tail_defect at hG
  linarith

/-- Paper-facing statement for
`thm:xi-time-part57f-convex-extension-affine-tail`. A convex tail defect that is nonnegative and
vanishes at every integer anchor from `a0` onward must vanish on the full real tail. -/
def xi_time_part57f_convex_extension_affine_tail_statement : Prop :=
  ∀ (Λ : ℝ → ℝ) (alphaStar gStar : ℝ) (a0 : ℕ),
    ConvexOn ℝ (Set.Ici (a0 : ℝ))
        (fun t => xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar t) →
      (∀ t : ℝ, (a0 : ℝ) ≤ t →
        0 ≤ xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar t) →
      (∀ n : ℕ, a0 ≤ n →
        xi_time_part57f_convex_extension_affine_tail_defect Λ alphaStar gStar (n : ℝ) = 0) →
      ∀ t : ℝ, (a0 : ℝ) ≤ t → Λ t = alphaStar * t + gStar

/-- Paper label: `thm:xi-time-part57f-convex-extension-affine-tail`. -/
theorem paper_xi_time_part57f_convex_extension_affine_tail :
    xi_time_part57f_convex_extension_affine_tail_statement := by
  intro Λ alphaStar gStar a0 hconv hnonneg hzero t ht
  let n : ℕ := Nat.floor t
  have ht_nonneg : 0 ≤ t := le_trans (Nat.cast_nonneg a0) ht
  have hn_le_t : (n : ℝ) ≤ t := Nat.floor_le ht_nonneg
  have ht_le_n1 : t ≤ ((n + 1 : ℕ) : ℝ) := by
    have hlt : t < (Nat.floor t : ℝ) + 1 := Nat.lt_floor_add_one t
    exact le_of_lt (by simpa [n] using hlt)
  have ha0_le_n : a0 ≤ n := by
    exact Nat.le_floor ht
  exact
    xi_time_part57f_convex_extension_affine_tail_unit_interval
      Λ alphaStar gStar a0 n hconv hnonneg hzero ha0_le_n t ⟨hn_le_t, ht_le_n1⟩

end Omega.Zeta
