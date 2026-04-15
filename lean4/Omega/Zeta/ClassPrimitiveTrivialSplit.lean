import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for separating the trivial channel from the
    primitive Peter--Weyl decomposition.
    lem:class-primitive-trivial-split -/
theorem paper_etds_class_primitive_trivial_split
    {Irr : Type}
    [Fintype Irr]
    [DecidableEq Irr]
    (triv : Irr)
    (classWeight pCount : ℂ)
    (charCoeff primitiveCoeff : Irr → ℂ)
    (hDecomp : pCount = classWeight * ∑ ρ, charCoeff ρ * primitiveCoeff ρ)
    (hTrivChar : charCoeff triv = 1)
    (hTrivCoeff : primitiveCoeff triv = pCount / classWeight) :
    pCount =
      classWeight * (pCount / classWeight) +
        classWeight *
          Finset.sum (Finset.univ.erase triv) (fun ρ => charCoeff ρ * primitiveCoeff ρ) := by
  have hsplit :
      (∑ ρ, charCoeff ρ * primitiveCoeff ρ) =
        Finset.sum (Finset.univ.erase triv) (fun ρ => charCoeff ρ * primitiveCoeff ρ) +
          charCoeff triv * primitiveCoeff triv := by
    have hmem : triv ∈ Finset.univ := by simp
    exact
      (Finset.sum_erase_add
        (s := Finset.univ)
        (a := triv)
        (f := fun ρ => charCoeff ρ * primitiveCoeff ρ)
        hmem).symm
  calc
    pCount = classWeight * ∑ ρ, charCoeff ρ * primitiveCoeff ρ := hDecomp
    _ =
        classWeight *
          (Finset.sum (Finset.univ.erase triv) (fun ρ => charCoeff ρ * primitiveCoeff ρ) +
            charCoeff triv * primitiveCoeff triv) := by
          rw [hsplit]
    _ =
        classWeight *
          (Finset.sum (Finset.univ.erase triv) (fun ρ => charCoeff ρ * primitiveCoeff ρ) +
            pCount / classWeight) := by
          simp [hTrivChar, hTrivCoeff]
    _ =
        classWeight * Finset.sum (Finset.univ.erase triv) (fun ρ => charCoeff ρ * primitiveCoeff ρ) +
          classWeight * (pCount / classWeight) := by
          rw [mul_add]
    _ =
        classWeight * (pCount / classWeight) +
          classWeight *
            Finset.sum (Finset.univ.erase triv) (fun ρ => charCoeff ρ * primitiveCoeff ρ) := by
          ac_rfl

end Omega.Zeta
