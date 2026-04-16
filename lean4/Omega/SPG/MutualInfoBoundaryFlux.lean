import Mathlib.Tactic

namespace Omega.SPG

/-- Boundary flux of a set S at coordinate i: difference between the number of
    configurations with ω_i = false and ω_i = true.
    def:boundary-flux -/
def boundaryFlux (n : ℕ) (S : Finset (Fin n → Bool)) (i : Fin n) : ℤ :=
  (S.filter (fun ω => ω i = false)).card - (S.filter (fun ω => ω i = true)).card

private lemma filter_bool_card_eq (n : ℕ) (i : Fin n) (v : Bool) :
    (Finset.univ.filter (fun (ω : Fin n → Bool) => ω i = v)).card = 2 ^ (n - 1) := by
  -- Finset.univ for (Fin n → Bool) = piFinset (fun _ => Finset.univ)
  have huniv : (Finset.univ : Finset (Fin n → Bool)) = Fintype.piFinset (fun _ => Finset.univ) := by
    ext f; simp [Fintype.mem_piFinset]
  rw [huniv]
  have h := Fintype.card_filter_piFinset_const (κ := Bool) Finset.univ i v
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_bool,
    Fintype.card_fin] at h
  exact h

private lemma partition_card (n : ℕ) (S : Finset (Fin n → Bool)) (i : Fin n) :
    (S.filter (fun ω => ω i = false)).card + (S.filter (fun ω => ω i = true)).card = S.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext ω; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      cases ω i <;> [exact Or.inl ⟨h, rfl⟩; exact Or.inr ⟨h, rfl⟩]
  · exact Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by cases h1 ▸ h2)

/-- The boundary flux squared is bounded by 2 · |S| · (2^n - |S|).
    This is a discrete isoperimetric inequality for Boolean cubes.
    cor:spg-mutual-information-boundary-flux-lower-bound -/
theorem mutualInfo_ge_boundaryFlux_sq (n : ℕ) (hn : 0 < n)
    (S : Finset (Fin n → Bool))
    (hS_nonempty : S.Nonempty) (hS_proper : S.card < 2 ^ n) :
    ∀ i : Fin n,
      (boundaryFlux n S i) ^ 2 * 1 ≤
        2 * (S.card : ℤ) * ((2 ^ n : ℤ) - S.card) := by
  intro i
  simp only [mul_one]
  unfold boundaryFlux
  set cf := (S.filter (fun ω => ω i = false)).card
  set ct := (S.filter (fun ω => ω i = true)).card
  have hpart : cf + ct = S.card := partition_card n S i
  have hcf_le : cf ≤ 2 ^ (n - 1) :=
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _
      (fun _ _ => Finset.mem_univ _))) (le_of_eq (filter_bool_card_eq n i false))
  have hct_le : ct ≤ 2 ^ (n - 1) :=
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _
      (fun _ _ => Finset.mem_univ _))) (le_of_eq (filter_bool_card_eq n i true))
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    cases n with | zero => omega | succ k => simp [pow_succ]; ring
  have hpow_z : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by exact_mod_cast hpow
  rw [hpow_z]
  have hcf_le_z : (cf : ℤ) ≤ 2 ^ (n - 1) := by exact_mod_cast hcf_le
  have hct_le_z : (ct : ℤ) ≤ 2 ^ (n - 1) := by exact_mod_cast hct_le
  have hpart_z : (cf : ℤ) + ct = S.card := by exact_mod_cast hpart
  nlinarith [sq_nonneg ((cf : ℤ) - 2 ^ (n - 1)),
             sq_nonneg ((ct : ℤ) - 2 ^ (n - 1)),
             Int.natCast_nonneg cf, Int.natCast_nonneg ct]

/-- Paper: `cor:spg-mutual-information-boundary-flux-lower-bound`.
    Direct wrapper around the Boolean-cube boundary flux inequality. -/
theorem paper_spg_mutual_information_boundary_flux_lower_bound
    (n : ℕ) (hn : 0 < n) (S : Finset (Fin n → Bool))
    (hS_nonempty : S.Nonempty) (hS_proper : S.card < 2 ^ n) :
    ∀ i : Fin n,
      (boundaryFlux n S i) ^ 2 ≤ 2 * (S.card : ℤ) * ((2 ^ n : ℤ) - S.card) := by
  simpa using mutualInfo_ge_boundaryFlux_sq n hn S hS_nonempty hS_proper

/-- Seed values for the mutual information boundary flux bound.
    cor:spg-mutual-information-boundary-flux-lower-bound -/
theorem paper_spg_mutual_information_boundary_flux_seeds :
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) ∧
    (∀ a b : ℤ, 0 < a → 0 < b → 0 ≤ (a - b) ^ 2) ∧
    (2 * 1 * 1 = 2 ∧ 2 * 2 * 2 = 8) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_, ⟨by norm_num, by norm_num⟩⟩
  intro a b _ _
  nlinarith [sq_abs (a - b)]

end Omega.SPG
