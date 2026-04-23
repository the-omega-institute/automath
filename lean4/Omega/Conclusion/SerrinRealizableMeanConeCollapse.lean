import Mathlib.Tactic

namespace Omega.Conclusion

/-- A realizable Serrin domain is modeled by a translation vector together with a positive scaling
parameter. -/
abbrev conclusion_serrin_realizable_mean_cone_collapse_domain (n : ℕ) :=
  (Fin n → ℝ) × {ρ : ℝ // 0 < ρ}

/-- The rigid representative `x₀ + ρ W_K`. -/
def conclusion_serrin_realizable_mean_cone_collapse_representative {n : ℕ}
    (WK : Fin n → ℝ) (Ω : conclusion_serrin_realizable_mean_cone_collapse_domain n) :
    Fin n → ℝ :=
  Ω.1 + Ω.2.1 • WK

/-- The vector-valued observable factors through the scaling parameter. -/
def conclusion_serrin_realizable_mean_cone_collapse_observable {n d : ℕ}
    (vWK : Fin d → ℝ) (Ω : conclusion_serrin_realizable_mean_cone_collapse_domain n) :
    Fin d → ℝ :=
  Ω.2.1 • vWK

/-- Positive ray spanned by the Wulff-shape observable. -/
def conclusion_serrin_realizable_mean_cone_collapse_positive_ray {d : ℕ}
    (v : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {w | ∃ ρ : ℝ, 0 < ρ ∧ w = ρ • v}

/-- Volume normalization fixes the scale parameter to `ρ = 1`. -/
def conclusion_serrin_realizable_mean_cone_collapse_normalized_image {n d : ℕ}
    (vWK : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.range (fun x0 : Fin n → ℝ =>
    conclusion_serrin_realizable_mean_cone_collapse_observable vWK (x0, ⟨1, zero_lt_one⟩))

/-- Paper label: `thm:conclusion-serrin-realizable-mean-cone-collapse`. The rigid realizable class
is exactly the translate-and-rescale family of a fixed Wulff shape, translation invariance removes
the basepoint, positive homogeneity leaves only the positive ray through `m_φ(W_K)`, and the
volume-normalized slice fixes the scalar to `1`. -/
def conclusion_serrin_realizable_mean_cone_collapse_statement : Prop :=
  ∀ {n d : ℕ} (WK : Fin n → ℝ) (vWK : Fin d → ℝ), vWK ≠ 0 →
    (∀ Ω : conclusion_serrin_realizable_mean_cone_collapse_domain n,
      conclusion_serrin_realizable_mean_cone_collapse_representative WK Ω =
        Ω.1 + Ω.2.1 • WK) ∧
    (∀ Ω : conclusion_serrin_realizable_mean_cone_collapse_domain n,
      conclusion_serrin_realizable_mean_cone_collapse_observable vWK Ω = Ω.2.1 • vWK) ∧
    ∃! v : Fin d → ℝ,
      v ≠ 0 ∧
        Set.range (conclusion_serrin_realizable_mean_cone_collapse_observable (n := n) vWK) =
          conclusion_serrin_realizable_mean_cone_collapse_positive_ray v ∧
        conclusion_serrin_realizable_mean_cone_collapse_normalized_image (n := n) vWK = {v}

theorem paper_conclusion_serrin_realizable_mean_cone_collapse :
    conclusion_serrin_realizable_mean_cone_collapse_statement := by
  unfold conclusion_serrin_realizable_mean_cone_collapse_statement
  intro n d WK vWK hvWK
  refine ⟨?_, ?_, ?_⟩
  · intro Ω
    rfl
  · intro Ω
    rfl
  · refine ⟨vWK, ?_, ?_⟩
    · refine ⟨hvWK, ?_, ?_⟩
      · ext w
        constructor
        · rintro ⟨Ω, rfl⟩
          exact ⟨Ω.2.1, Ω.2.2, rfl⟩
        · rintro ⟨ρ, hρ, rfl⟩
          exact ⟨(0, ⟨ρ, hρ⟩), by simp [conclusion_serrin_realizable_mean_cone_collapse_observable]⟩
      · ext w
        constructor
        · rintro ⟨x0, rfl⟩
          simp [conclusion_serrin_realizable_mean_cone_collapse_observable]
        · rintro rfl
          exact ⟨0, by simp [conclusion_serrin_realizable_mean_cone_collapse_observable]⟩
    · intro v hv
      have hvMem :
          vWK ∈ conclusion_serrin_realizable_mean_cone_collapse_normalized_image (n := n) vWK := by
        refine ⟨0, ?_⟩
        simp [conclusion_serrin_realizable_mean_cone_collapse_observable]
      have : vWK ∈ ({v} : Set (Fin d → ℝ)) := by
        simpa [hv.2.2] using hvMem
      exact this.symm

end Omega.Conclusion
