import Mathlib.Data.Fintype.Card

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: deterministic unique recovery requires at least as many side-information
codes as candidates.
    cor:group-jg-side-information-bit-lower-bound -/
theorem paper_gut_side_information_bit_lower_bound_seeds
    {Candidate Code : Type*} [Fintype Candidate] [Fintype Code]
    (encode : Candidate → Code) (hinj : Function.Injective encode) :
    Fintype.card Candidate ≤ Fintype.card Code :=
  Fintype.card_le_of_injective encode hinj

set_option maxHeartbeats 400000 in
/-- Packaged form of the side-information lower-bound seed.
    cor:group-jg-side-information-bit-lower-bound -/
theorem paper_gut_side_information_bit_lower_bound_package
    {Candidate Code : Type*} [Fintype Candidate] [Fintype Code]
    (encode : Candidate → Code) (hinj : Function.Injective encode) :
    Fintype.card Candidate ≤ Fintype.card Code :=
  paper_gut_side_information_bit_lower_bound_seeds encode hinj

end Omega.GU
