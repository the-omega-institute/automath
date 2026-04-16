import Mathlib.Tactic

namespace Omega.CircleDimension

private lemma chain_left_mono {Cert : Type*} (left right : Cert → ℝ) (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
          Set.Icc (left (chain n)) (right (chain n)))
    (hclosed : ∀ n, left (chain n) ≤ right (chain n)) :
    Monotone (fun n => left (chain n)) := by
  intro m n hmn
  induction hmn with
  | refl =>
      exact le_rfl
  | @step n _ ih =>
      have hmem :
          left (chain (n + 1)) ∈
            Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) :=
        ⟨le_rfl, hclosed (n + 1)⟩
      exact le_trans ih (hnested n hmem).1

private lemma chain_right_anti {Cert : Type*} (left right : Cert → ℝ) (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
          Set.Icc (left (chain n)) (right (chain n)))
    (hclosed : ∀ n, left (chain n) ≤ right (chain n)) :
    Antitone (fun n => right (chain n)) := by
  intro m n hmn
  induction hmn with
  | refl =>
      exact le_rfl
  | @step n _ ih =>
      have hmem :
          right (chain (n + 1)) ∈
            Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) :=
        ⟨hclosed (n + 1), le_rfl⟩
      exact le_trans (hnested n hmem).2 ih

private lemma eq_of_mem_nested_intervals {Cert : Type*} (left right : Cert → ℝ) (chain : ℕ → Cert)
    (hdiam :
      ∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε)
    {θ η : ℝ}
    (hθ : ∀ n, θ ∈ Set.Icc (left (chain n)) (right (chain n)))
    (hη : ∀ n, η ∈ Set.Icc (left (chain n)) (right (chain n))) :
    θ = η := by
  by_contra hne
  have hpos : 0 < |θ - η| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := hdiam |θ - η| hpos
  have hsmall : right (chain N) - left (chain N) < |θ - η| := hN N le_rfl
  have hθN := hθ N
  have hηN := hη N
  have hgap :
      |θ - η| ≤ right (chain N) - left (chain N) := by
    rcases le_total θ η with hle | hle
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      nlinarith [hθN.1, hθN.2, hηN.1, hηN.2]
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      nlinarith [hθN.1, hθN.2, hηN.1, hηN.2]
  linarith

/-- Paper-facing inverse-limit addressing package: nested closed certificate intervals with
shrinking diameters determine a unique point, and all valid certificates for that point merge
into a single equivalence class.
    prop:cdim-certificate-inverse-limit-addressing -/
theorem paper_cdim_certificate_inverse_limit_addressing {Cert : Type*}
    (pointsTo : Cert → ℝ → Prop) (equiv : Cert → Cert → Prop) (left right : Cert → ℝ)
    (chain : ℕ → Cert)
    (hnested :
      ∀ n,
        Set.Icc (left (chain (n + 1))) (right (chain (n + 1))) ⊆
          Set.Icc (left (chain n)) (right (chain n)))
    (hdiam :
      ∀ ε > 0, ∃ N, ∀ n ≥ N, right (chain n) - left (chain n) < ε)
    (hclosed : ∀ n, left (chain n) ≤ right (chain n))
    (hmerge : ∀ C C' θ, pointsTo C θ → pointsTo C' θ → equiv C C') :
    ∃! θ : ℝ,
      (∀ n, θ ∈ Set.Icc (left (chain n)) (right (chain n))) ∧
        ∀ C C', pointsTo C θ → pointsTo C' θ → equiv C C' := by
  let S : Set ℝ := Set.range fun n => left (chain n)
  have hleftMono : Monotone (fun n => left (chain n)) :=
    chain_left_mono left right chain hnested hclosed
  have hrightAnti : Antitone (fun n => right (chain n)) :=
    chain_right_anti left right chain hnested hclosed
  have hupper : ∀ n, ∀ x ∈ S, x ≤ right (chain n) := by
    intro n x hx
    rcases hx with ⟨m, rfl⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact le_trans (hleftMono hmn) (hclosed n)
    · exact le_trans (hclosed m) (hrightAnti hnm)
  have hSnonempty : S.Nonempty := ⟨left (chain 0), ⟨0, rfl⟩⟩
  have hSbdd : BddAbove S := ⟨right (chain 0), hupper 0⟩
  refine ⟨sSup S, ?_, ?_⟩
  · constructor
    · intro n
      refine ⟨le_csSup hSbdd ⟨n, rfl⟩, csSup_le hSnonempty (hupper n)⟩
    · intro C C' hC hC'
      exact hmerge C C' (sSup S) hC hC'
  · intro θ hθ
    exact eq_of_mem_nested_intervals left right chain hdiam hθ.1 (by
      intro n
      exact ⟨le_csSup hSbdd ⟨n, rfl⟩, csSup_le hSnonempty (hupper n)⟩)

end Omega.CircleDimension
