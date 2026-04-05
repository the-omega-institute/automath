import Omega.Zeta.HankelVandermonde2
import Mathlib.Tactic

namespace Omega.Zeta

def hankel3DetScalar (s0 s1 s2 s3 s4 : ℤ) : ℤ :=
  s0 * (s2 * s4 - s3 * s3) - s1 * (s1 * s4 - s2 * s3) + s2 * (s1 * s3 - s2 * s2)

def hankelMoment0 (ω1 ω2 ω3 : ℤ) : ℤ := ω1 + ω2 + ω3
def hankelMoment1 (ω1 ω2 ω3 a1 a2 a3 : ℤ) : ℤ := ω1*a1 + ω2*a2 + ω3*a3
def hankelMoment2 (ω1 ω2 ω3 a1 a2 a3 : ℤ) : ℤ := ω1*a1^2 + ω2*a2^2 + ω3*a3^2
def hankelMoment3 (ω1 ω2 ω3 a1 a2 a3 : ℤ) : ℤ := ω1*a1^3 + ω2*a2^3 + ω3*a3^3
def hankelMoment4 (ω1 ω2 ω3 a1 a2 a3 : ℤ) : ℤ := ω1*a1^4 + ω2*a2^4 + ω3*a3^4

/-- Pre-expanded 3×3 Hankel–Vandermonde square law.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel3_vandermonde_square_scalar
    (ω1 ω2 ω3 a1 a2 a3 : ℤ) :
    hankel3DetScalar
      (hankelMoment0 ω1 ω2 ω3)
      (hankelMoment1 ω1 ω2 ω3 a1 a2 a3)
      (hankelMoment2 ω1 ω2 ω3 a1 a2 a3)
      (hankelMoment3 ω1 ω2 ω3 a1 a2 a3)
      (hankelMoment4 ω1 ω2 ω3 a1 a2 a3)
    = ω1 * ω2 * ω3 * (a2 - a1)^2 * (a3 - a1)^2 * (a3 - a2)^2 := by
  unfold hankel3DetScalar hankelMoment0 hankelMoment1 hankelMoment2 hankelMoment3 hankelMoment4
  ring

/-- Hankel-Vandermonde package.
    cor:xi-hankel-vs-prony-square-gap -/
theorem paper_hankel_vandermonde_package :
    (∀ ω1 ω2 a1 a2 : ℤ, hankel2 ω1 ω2 a1 a2 = ω1 * ω2 * (a2 - a1) ^ 2) ∧
    (∀ ω1 ω2 ω3 : ℤ, hankelMoment0 ω1 ω2 ω3 = ω1 + ω2 + ω3) ∧
    hankel2 1 1 0 1 = 1 ∧
    hankel2 3 5 1 2 = 15 :=
  ⟨hankel2_vandermonde_square, fun _ _ _ => rfl,
   by native_decide, by native_decide⟩

end Omega.Zeta
