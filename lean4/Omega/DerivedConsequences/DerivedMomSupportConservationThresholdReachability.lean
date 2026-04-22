import Mathlib.Tactic
import Omega.POM.AnomSwapLowerboundAndMomAmplify

namespace Omega.DerivedConsequences

noncomputable section

/-- Coordinatewise `q`-fold MOM amplification on a finite anomaly profile. -/
def derived_mom_support_conservation_threshold_reachability_mom {d : ℕ}
    (q : ℕ) (a : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (q : ℝ) * a i

/-- The nonzero support of a finite anomaly profile. -/
def derived_mom_support_conservation_threshold_reachability_support {d : ℕ}
    (a : Fin d → ℝ) : Set (Fin d) :=
  {i | a i ≠ 0}

/-- Sup norm on the finite Pontryagin-dual coordinate set, realized as the maximum absolute
coordinate. -/
noncomputable def derived_mom_support_conservation_threshold_reachability_sup_norm {d : ℕ}
    (hd : 0 < d) (a : Fin d → ℝ) : ℝ :=
  let s : Finset ℝ := Finset.univ.image fun i : Fin d => |a i|
  s.max' <| by
    refine ⟨|a ⟨0, hd⟩|, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, hd⟩, Finset.mem_univ _, rfl⟩

lemma derived_mom_support_conservation_threshold_reachability_le_sup_norm {d : ℕ}
    (hd : 0 < d) (a : Fin d → ℝ) (i : Fin d) :
    |a i| ≤ derived_mom_support_conservation_threshold_reachability_sup_norm hd a := by
  unfold derived_mom_support_conservation_threshold_reachability_sup_norm
  exact Finset.le_max' (s := Finset.univ.image fun j : Fin d => |a j|) _ <|
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

lemma derived_mom_support_conservation_threshold_reachability_exists_max {d : ℕ}
    (hd : 0 < d) (a : Fin d → ℝ) :
    ∃ i : Fin d,
      derived_mom_support_conservation_threshold_reachability_sup_norm hd a = |a i| := by
  unfold derived_mom_support_conservation_threshold_reachability_sup_norm
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image fun j : Fin d => |a j|)
      ⟨|a ⟨0, hd⟩|, Finset.mem_image.mpr ⟨⟨0, hd⟩, Finset.mem_univ _, rfl⟩⟩)
  exact ⟨i, hi.symm⟩

lemma derived_mom_support_conservation_threshold_reachability_sup_norm_mom {d : ℕ}
    (hd : 0 < d) (q : ℕ) (a : Fin d → ℝ) :
    derived_mom_support_conservation_threshold_reachability_sup_norm hd
        (derived_mom_support_conservation_threshold_reachability_mom q a) =
      (q : ℝ) * derived_mom_support_conservation_threshold_reachability_sup_norm hd a := by
  have hupper :
      derived_mom_support_conservation_threshold_reachability_sup_norm hd
          (derived_mom_support_conservation_threshold_reachability_mom q a) ≤
        (q : ℝ) * derived_mom_support_conservation_threshold_reachability_sup_norm hd a := by
    unfold derived_mom_support_conservation_threshold_reachability_sup_norm
      derived_mom_support_conservation_threshold_reachability_mom
    change
      (Finset.univ.image fun i : Fin d => |(q : ℝ) * a i|).max' _ ≤
        (q : ℝ) * (Finset.univ.image fun i : Fin d => |a i|).max' _
    apply Finset.max'_le (s := Finset.univ.image fun i : Fin d => |(q : ℝ) * a i|)
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ q by exact_mod_cast Nat.zero_le q)]
    exact mul_le_mul_of_nonneg_left
      (derived_mom_support_conservation_threshold_reachability_le_sup_norm hd a i)
      (show (0 : ℝ) ≤ q by exact_mod_cast Nat.zero_le q)
  obtain ⟨i, hi⟩ := derived_mom_support_conservation_threshold_reachability_exists_max hd a
  have hlower :
      (q : ℝ) * derived_mom_support_conservation_threshold_reachability_sup_norm hd a ≤
        derived_mom_support_conservation_threshold_reachability_sup_norm hd
          (derived_mom_support_conservation_threshold_reachability_mom q a) := by
    rw [hi]
    have hmem :
        |(derived_mom_support_conservation_threshold_reachability_mom q a) i| ∈
          Finset.univ.image
            (fun j : Fin d =>
              |derived_mom_support_conservation_threshold_reachability_mom q a j|) := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hle :
        |derived_mom_support_conservation_threshold_reachability_mom q a i| ≤
          derived_mom_support_conservation_threshold_reachability_sup_norm hd
            (derived_mom_support_conservation_threshold_reachability_mom q a) := by
      unfold derived_mom_support_conservation_threshold_reachability_sup_norm
      exact Finset.le_max' (s := Finset.univ.image
        (fun j : Fin d => |derived_mom_support_conservation_threshold_reachability_mom q a j|)) _ hmem
    simpa [derived_mom_support_conservation_threshold_reachability_mom, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ q by exact_mod_cast Nat.zero_le q)] using hle
  exact le_antisymm hupper hlower

/-- Paper label: `prop:derived-mom-support-conservation-threshold-reachability`. In the finite
Pontryagin-dual coordinate model, `MOM_q` amplifies every coordinate by the nonzero scalar `q`,
so nonzero support is preserved, the sup norm scales by exactly `q`, and any threshold below
`q · ‖a‖_∞` is therefore reachable after choosing such a `q`. -/
theorem paper_derived_mom_support_conservation_threshold_reachability {d : ℕ}
    (hd : 0 < d) (a : Fin d → ℝ) (q : ℕ) (hq : 0 < q) (τ : ℝ)
    (hreach :
      τ ≤ (q : ℝ) * derived_mom_support_conservation_threshold_reachability_sup_norm hd a) :
    ‖derived_mom_support_conservation_threshold_reachability_mom q a‖ = q * ‖a‖ ∧
      derived_mom_support_conservation_threshold_reachability_support
          (derived_mom_support_conservation_threshold_reachability_mom q a) =
        derived_mom_support_conservation_threshold_reachability_support a ∧
      derived_mom_support_conservation_threshold_reachability_sup_norm hd
          (derived_mom_support_conservation_threshold_reachability_mom q a) =
        (q : ℝ) * derived_mom_support_conservation_threshold_reachability_sup_norm hd a ∧
      τ ≤ derived_mom_support_conservation_threshold_reachability_sup_norm hd
        (derived_mom_support_conservation_threshold_reachability_mom q a) := by
  have hAmp :
      derived_mom_support_conservation_threshold_reachability_mom q a = (q : ℝ) • a := by
    ext i
    simp [derived_mom_support_conservation_threshold_reachability_mom]
  have hnorm :
      ‖derived_mom_support_conservation_threshold_reachability_mom q a‖ = q * ‖a‖ := by
    simpa [one_mul] using
      Omega.POM.moment_amplify_norm
        (Anom := fun v : Fin d → ℝ => v)
        (MOM := derived_mom_support_conservation_threshold_reachability_mom)
        q a hAmp
  have hsupport :
      derived_mom_support_conservation_threshold_reachability_support
          (derived_mom_support_conservation_threshold_reachability_mom q a) =
        derived_mom_support_conservation_threshold_reachability_support a := by
    ext i
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simp [derived_mom_support_conservation_threshold_reachability_support,
      derived_mom_support_conservation_threshold_reachability_mom, hqR]
  have hsup :
      derived_mom_support_conservation_threshold_reachability_sup_norm hd
          (derived_mom_support_conservation_threshold_reachability_mom q a) =
        (q : ℝ) * derived_mom_support_conservation_threshold_reachability_sup_norm hd a :=
    derived_mom_support_conservation_threshold_reachability_sup_norm_mom hd q a
  refine ⟨hnorm, hsupport, hsup, ?_⟩
  simpa [hsup] using hreach

end

end Omega.DerivedConsequences
