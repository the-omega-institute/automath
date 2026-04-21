import Mathlib.Tactic

namespace Omega.POM

/-- Finite-support Stieltjes transform attached to a list of secular poles. -/
def stieltjesPoleSum (poles : List ℚ) (z : ℚ) : ℚ :=
  (poles.map fun t => 1 / (t - z)).sum

/-- One tensor step: pairwise products of the pole lists. -/
def tensorPoleStep : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | t :: poles₁, poles₂ => poles₂.map (fun u => t * u) ++ tensorPoleStep poles₁ poles₂

/-- Iterated tensor-product pole list. -/
def tensorPoleList : List (List ℚ) → List ℚ
  | [] => []
  | [poles] => poles
  | poles :: rest => tensorPoleStep poles (tensorPoleList rest)

/-- Recursive expansion of the tensor Stieltjes transform. -/
def stieltjesTensorExpansion : List (List ℚ) → ℚ → ℚ
  | [], _ => 0
  | [poles], z => stieltjesPoleSum poles z
  | poles :: rest, z =>
      (poles.map fun t => (1 / t) * stieltjesTensorExpansion rest (z / t)).sum

/-- Every pole recorded in the tensor family is nonzero. -/
def PoleFamilyNonzero : List (List ℚ) → Prop
  | [] => True
  | poles :: rest => (∀ t ∈ poles, t ≠ 0) ∧ PoleFamilyNonzero rest

private lemma scaled_stieltjes_term (t u z : ℚ) (ht : t ≠ 0) :
    1 / (t * u - z) = (1 / t) * (1 / (u - z / t)) := by
  by_cases hden : t * u - z = 0
  · have huz : u - z / t = 0 := by
      apply sub_eq_zero.mpr
      apply (eq_div_iff ht).2
      linarith
    simp [hden, huz]
  · have huz : u - z / t ≠ 0 := by
      intro huz
      apply hden
      have hmul : u * t = z := by
        apply (eq_div_iff ht).1
        exact sub_eq_zero.mp huz
      linarith [hmul]
    field_simp [ht, hden, huz]

private lemma stieltjes_scale_out (poles : List ℚ) (t z : ℚ) (ht : t ≠ 0) :
    stieltjesPoleSum (poles.map fun u => t * u) z =
      (1 / t) * stieltjesPoleSum poles (z / t) := by
  induction poles with
  | nil =>
      simp [stieltjesPoleSum]
  | cons u poles ih =>
      simp [stieltjesPoleSum] at ih ⊢
      have hterm : (t * u - z)⁻¹ = t⁻¹ * (u - z / t)⁻¹ := by
        simpa [one_div] using scaled_stieltjes_term t u z ht
      rw [hterm, ih]
      ring

/-- One-step tensor Stieltjes recursion. -/
private theorem stieltjes_tensor_recursion_one_step
    (poles₁ poles₂ : List ℚ) (z : ℚ) (h₁ : ∀ t ∈ poles₁, t ≠ 0) :
    stieltjesPoleSum (tensorPoleStep poles₁ poles₂) z =
      (poles₁.map fun t => (1 / t) * stieltjesPoleSum poles₂ (z / t)).sum := by
  induction poles₁ with
  | nil =>
      simp [tensorPoleStep, stieltjesPoleSum]
  | cons t poles ih =>
      have ht : t ≠ 0 := h₁ t (by simp)
      have hpoles : ∀ s ∈ poles, s ≠ 0 := by
        intro s hs
        exact h₁ s (by simp [hs])
      simp [tensorPoleStep, stieltjesPoleSum]
      have hhead :
          (List.map ((fun s => (s - z)⁻¹) ∘ fun u => t * u) poles₂).sum =
            t⁻¹ * (List.map (fun s => (s - z / t)⁻¹) poles₂).sum := by
        simpa [stieltjesPoleSum, one_div] using stieltjes_scale_out poles₂ t z ht
      have htail :
          (List.map (fun s => (s - z)⁻¹) (tensorPoleStep poles poles₂)).sum =
            (List.map (fun s => s⁻¹ * (List.map (fun u => (u - z / s)⁻¹) poles₂).sum) poles).sum := by
        simpa [stieltjesPoleSum, one_div] using ih hpoles
      rw [hhead, htail]

/-- Paper label: `cor:pom-diagonal-rate-critical-spectrum-stieltjes-tensor-recursion-kfold`. -/
theorem paper_pom_diagonal_rate_critical_spectrum_stieltjes_tensor_recursion_kfold
    (families : List (List ℚ)) (z : ℚ) (hfamilies : PoleFamilyNonzero families) :
    stieltjesPoleSum (tensorPoleList families) z = stieltjesTensorExpansion families z := by
  induction families generalizing z with
  | nil =>
      simp [tensorPoleList, stieltjesTensorExpansion, stieltjesPoleSum]
  | cons poles rest ih =>
      rcases hfamilies with ⟨hpoles, hrest⟩
      cases rest with
      | nil =>
          simp [tensorPoleList, stieltjesTensorExpansion]
      | cons next tail =>
          calc
            stieltjesPoleSum (tensorPoleList (poles :: next :: tail)) z
                = stieltjesPoleSum (tensorPoleStep poles (tensorPoleList (next :: tail))) z := by
                    rfl
            _ = (poles.map fun t => (1 / t) * stieltjesPoleSum (tensorPoleList (next :: tail))
                  (z / t)).sum := by
                    exact stieltjes_tensor_recursion_one_step poles (tensorPoleList (next :: tail))
                      z hpoles
            _ = (poles.map fun t => (1 / t) * stieltjesTensorExpansion (next :: tail)
                  (z / t)).sum := by
                    clear hpoles
                    induction poles with
                    | nil =>
                        simp
                    | cons t poles ihp =>
                        simp [ih (z / t) hrest]
                        simpa [one_div] using ihp
            _ = stieltjesTensorExpansion (poles :: next :: tail) z := by
                    rfl

end Omega.POM
