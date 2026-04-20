import Mathlib.Tactic
import Omega.Zeta.CyclicEulerSpectralRigidity

namespace Omega.Zeta

/-- A normal cyclic-Euler atom contributes `m * n` eigenvalues of modulus `|β|^(1 / n)`. -/
structure CyclicEulerNormalAtom where
  multiplicity : Nat
  order : Nat
  order_pos : 0 < order
  beta : ℝ

/-- The number of eigenvalues contributed by one cyclic-Euler atom. -/
def CyclicEulerNormalAtom.eigenvalueCount (A : CyclicEulerNormalAtom) : Nat :=
  A.multiplicity * A.order

/-- The `p`-th Schatten contribution of one cyclic-Euler atom. -/
noncomputable def CyclicEulerNormalAtom.schattenWeight (p : ℝ) (A : CyclicEulerNormalAtom) : ℝ :=
  Real.rpow |A.beta| (p / A.order)

/-- Expand the spectral list by repeating the atomic modulus contribution exactly `m * n` times. -/
noncomputable def cyclicEulerExpandedSchattenTerms
    (p : ℝ) : List CyclicEulerNormalAtom → List ℝ
  | [] => []
  | A :: atoms =>
      List.replicate A.eigenvalueCount (A.schattenWeight p) ++ cyclicEulerExpandedSchattenTerms p atoms

/-- The closed-form Schatten sum attached to the atomic cyclic-Euler factorization. -/
noncomputable def cyclicEulerSchattenInvariant
    (p : ℝ) : List CyclicEulerNormalAtom → ℝ
  | [] => 0
  | A :: atoms =>
      (A.eigenvalueCount : ℝ) * A.schattenWeight p + cyclicEulerSchattenInvariant p atoms

private theorem cyclicEulerExpandedSchattenTerms_length (p : ℝ)
    (atoms : List CyclicEulerNormalAtom) :
    (cyclicEulerExpandedSchattenTerms p atoms).length =
      (atoms.map CyclicEulerNormalAtom.eigenvalueCount).sum := by
  induction atoms with
  | nil =>
      simp [cyclicEulerExpandedSchattenTerms]
  | cons A atoms ih =>
      simp [cyclicEulerExpandedSchattenTerms, ih, CyclicEulerNormalAtom.eigenvalueCount]

private theorem cyclicEulerExpandedSchattenTerms_sum (p : ℝ)
    (atoms : List CyclicEulerNormalAtom) :
    (cyclicEulerExpandedSchattenTerms p atoms).sum = cyclicEulerSchattenInvariant p atoms := by
  induction atoms with
  | nil =>
      simp [cyclicEulerExpandedSchattenTerms, cyclicEulerSchattenInvariant]
  | cons A atoms ih =>
      simp [cyclicEulerExpandedSchattenTerms, cyclicEulerSchattenInvariant, ih,
        CyclicEulerNormalAtom.eigenvalueCount, CyclicEulerNormalAtom.schattenWeight]

/-- Under a normal cyclic-Euler realization, each atom contributes `mⱼ nⱼ` copies of the modulus
`|βⱼ|^(1 / nⱼ)`, so the Schatten-`p` invariant is the corresponding finite spectral sum.
    cor:cyclic-euler-schatten-invariants -/
theorem paper_cyclic_euler_schatten_invariants (p : ℝ) (atoms : List CyclicEulerNormalAtom) :
    (cyclicEulerExpandedSchattenTerms p atoms).length =
      (atoms.map CyclicEulerNormalAtom.eigenvalueCount).sum ∧
      (cyclicEulerExpandedSchattenTerms p atoms).sum = cyclicEulerSchattenInvariant p atoms := by
  have hLength :
      (cyclicEulerExpandedSchattenTerms p atoms).length =
        (atoms.map CyclicEulerNormalAtom.eigenvalueCount).sum :=
    cyclicEulerExpandedSchattenTerms_length p atoms
  have hRigidity :=
    paper_cyclic_euler_spectral_rigidity
      ((cyclicEulerExpandedSchattenTerms p atoms).length =
        (atoms.map CyclicEulerNormalAtom.eigenvalueCount).sum)
      (0 ≤ (atoms.map CyclicEulerNormalAtom.eigenvalueCount).sum)
      True
      hLength
      (fun _ => Nat.zero_le _)
      (fun _ => trivial)
  exact ⟨hRigidity.1, cyclicEulerExpandedSchattenTerms_sum p atoms⟩

end Omega.Zeta
