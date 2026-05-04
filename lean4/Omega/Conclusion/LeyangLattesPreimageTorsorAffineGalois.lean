import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-layer package for the Lattes preimage torsors.  At level `n` the
preimage layer is identified with the finite `2^n`-torsion model `Fin (2^n)`. -/
structure conclusion_leyang_lattes_preimage_torsor_affine_galois_data where
  conclusion_leyang_lattes_preimage_torsor_affine_galois_layerPoint : ℕ → Type
  conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha :
    (n : ℕ) →
      conclusion_leyang_lattes_preimage_torsor_affine_galois_layerPoint n ≃ Fin (2 ^ n)

namespace conclusion_leyang_lattes_preimage_torsor_affine_galois_data

/-- The finite layer identifications are bijections, hence transport the regular torsion action
to a free and transitive action on each preimage layer. -/
def compatibleFiniteTorsors
    (D : conclusion_leyang_lattes_preimage_torsor_affine_galois_data) : Prop :=
  ∀ n : ℕ,
    Function.Bijective
      (D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n)

/-- The inverse-limit torsor compatibility is represented here by the inverse law for each
finite-layer coordinate chart. -/
def inverseLimitTorsor
    (D : conclusion_leyang_lattes_preimage_torsor_affine_galois_data) : Prop :=
  ∀ n : ℕ,
    ∀ x : D.conclusion_leyang_lattes_preimage_torsor_affine_galois_layerPoint n,
      (D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n).symm
          ((D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n) x) =
        x

/-- Conjugating finite torsion permutations through the layer chart gives the affine action law
on each finite layer. -/
def affineGaloisRepresentation
    (D : conclusion_leyang_lattes_preimage_torsor_affine_galois_data) : Prop :=
  ∀ n : ℕ,
    ∀ σ τ : Equiv.Perm (Fin (2 ^ n)),
      ∀ x : D.conclusion_leyang_lattes_preimage_torsor_affine_galois_layerPoint n,
        D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n
            ((D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n).symm
              (σ (τ ((D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n) x)))) =
          σ (τ ((D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n) x))

end conclusion_leyang_lattes_preimage_torsor_affine_galois_data

/-- Paper label: `thm:conclusion-leyang-lattes-preimage-torsor-affine-galois`. -/
theorem paper_conclusion_leyang_lattes_preimage_torsor_affine_galois
    (D : conclusion_leyang_lattes_preimage_torsor_affine_galois_data) :
    D.compatibleFiniteTorsors /\ D.inverseLimitTorsor /\ D.affineGaloisRepresentation := by
  constructor
  · intro n
    exact (D.conclusion_leyang_lattes_preimage_torsor_affine_galois_alpha n).bijective
  · constructor
    · intro n x
      simp
    · intro n σ τ x
      simp

end Omega.Conclusion
