import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Decode a coefficient list into the multiplicity spectrum by taking absolute values. -/
def pom_trivial_channel_finite_decidability_decodeFiberSpectrum (code : List Int) : List ℕ :=
  code.map Int.natAbs

/-- Collision moments are the power sums of the recovered multiplicities. -/
def pom_trivial_channel_finite_decidability_collisionMoment (spectrum : List ℕ) (q : ℕ) : ℕ :=
  (spectrum.map fun d => d ^ q).sum

/-- A concrete Schur-channel statistic built from the same multiplicity spectrum. -/
def pom_trivial_channel_finite_decidability_schurChannelValue
    (spectrum : List ℕ) (q : ℕ) : ℕ :=
  (spectrum.map fun d => d * d ^ q).sum

/-- Concrete finite data for the trivial-channel finite decidability package. The coefficient
window records the inverse series numerator `Q_m`, the kernel series records `H_m`, and the fiber
spectrum is decoded from the recovered coefficient list. -/
structure PomTrivialChannelFiniteDecidabilityData where
  order : ℕ
  recurrenceCoeff : ℕ → Int
  kernelSeries : ℕ → Int
  signal : ℕ → Int
  qWindow : ℕ → Int
  fiberSpectrum : List ℕ
  convolutionIdentity :
    ∀ n, n ≤ order →
      Finset.sum (Finset.range (n + 1))
          (fun i => recurrenceCoeff i * kernelSeries (n - i)) =
        if n = 0 then 1 else 0
  windowMatchesCoefficients :
    ∀ i, i < order → qWindow i = recurrenceCoeff i
  signalRecurrence :
    ∀ n,
      signal (n + order) =
        -(Finset.sum Finset.univ
          (fun i : Fin order =>
            recurrenceCoeff i.1 * signal (n + i.1)))
  fiberSpectrumFromCoefficients :
    fiberSpectrum =
      pom_trivial_channel_finite_decidability_decodeFiberSpectrum
        (List.ofFn fun i : Fin (order + 1) => recurrenceCoeff i.1)

namespace PomTrivialChannelFiniteDecidabilityData

/-- The coefficient of `z^n` in the truncated product `Q_m(z) H_m(z)`. -/
def pom_trivial_channel_finite_decidability_convolutionCoefficient
    (D : PomTrivialChannelFiniteDecidabilityData) (n : ℕ) : Int :=
  Finset.sum (Finset.range (n + 1))
    (fun i => D.recurrenceCoeff i * D.kernelSeries (n - i))

/-- Recover the numerator coefficients from the finite window by reading the first `m` entries
from `qWindow` and the final entry from the stored monic coefficient list. -/
def pom_trivial_channel_finite_decidability_recoveredQ
    (D : PomTrivialChannelFiniteDecidabilityData) : ℕ → Int := fun i =>
  if i < D.order then D.qWindow i else D.recurrenceCoeff i

/-- Decode the coefficient list recovered from the finite window into the fiber spectrum. -/
def pom_trivial_channel_finite_decidability_recoveredFiberSpectrum
    (D : PomTrivialChannelFiniteDecidabilityData) : List ℕ :=
  pom_trivial_channel_finite_decidability_decodeFiberSpectrum
    (List.ofFn fun i : Fin (D.order + 1) =>
      pom_trivial_channel_finite_decidability_recoveredQ D i.1)

/-- The generating-function identity and the order-`m` recurrence are both visible from the
finite coefficient window. -/
def windowDeterminesRecurrence (D : PomTrivialChannelFiniteDecidabilityData) : Prop :=
  (∀ n, n ≤ D.order →
    pom_trivial_channel_finite_decidability_convolutionCoefficient D n = if n = 0 then 1 else 0) ∧
    (∀ n,
      D.signal (n + D.order) =
        -(Finset.sum Finset.univ
          (fun i : Fin D.order =>
            D.recurrenceCoeff i.1 * D.signal (n + i.1)))) ∧
    pom_trivial_channel_finite_decidability_recoveredQ D = D.recurrenceCoeff

/-- Once the recurrence coefficients are known, the trivial-channel fiber spectrum is recovered by
decoding the coefficient list. -/
def recurrenceDeterminesFiberSpectrum (D : PomTrivialChannelFiniteDecidabilityData) : Prop :=
  D.fiberSpectrum = pom_trivial_channel_finite_decidability_recoveredFiberSpectrum D

/-- The recovered spectrum determines the collision moments and the Schur-channel values through
their symmetric power-sum formulas. -/
def collisionMoments (D : PomTrivialChannelFiniteDecidabilityData) : ℕ → ℕ :=
  pom_trivial_channel_finite_decidability_collisionMoment D.fiberSpectrum

/-- The Schur-channel statistics attached to the recovered spectrum. -/
def schurChannelValues (D : PomTrivialChannelFiniteDecidabilityData) : ℕ → ℕ :=
  pom_trivial_channel_finite_decidability_schurChannelValue D.fiberSpectrum

/-- Moments and Schur statistics are reconstructed by evaluating the corresponding power sums on
the recovered multiplicity spectrum. -/
def fiberSpectrumDeterminesMomentsAndSchur
    (D : PomTrivialChannelFiniteDecidabilityData) : Prop :=
  (∀ q,
      D.collisionMoments q =
        pom_trivial_channel_finite_decidability_collisionMoment
          (pom_trivial_channel_finite_decidability_recoveredFiberSpectrum D) q) ∧
    (∀ q,
      D.schurChannelValues q =
        pom_trivial_channel_finite_decidability_schurChannelValue
          (pom_trivial_channel_finite_decidability_recoveredFiberSpectrum D) q)

lemma pom_trivial_channel_finite_decidability_recoveredQ_eq
    (D : PomTrivialChannelFiniteDecidabilityData) :
    pom_trivial_channel_finite_decidability_recoveredQ D = D.recurrenceCoeff := by
  funext i
  by_cases h : i < D.order
  · simpa [pom_trivial_channel_finite_decidability_recoveredQ, h] using
      D.windowMatchesCoefficients i h
  · rw [pom_trivial_channel_finite_decidability_recoveredQ, if_neg h]

end PomTrivialChannelFiniteDecidabilityData

open PomTrivialChannelFiniteDecidabilityData

/-- Paper label: `prop:pom-trivial-channel-finite-decidability`. A finite window of the trivial
channel determines the inverse-series recurrence, the recovered recurrence determines the fiber
multiplicity spectrum, and the spectrum in turn determines the collision moments and Schur-channel
statistics. -/
theorem paper_pom_trivial_channel_finite_decidability (D : PomTrivialChannelFiniteDecidabilityData) :
    D.windowDeterminesRecurrence ∧ D.recurrenceDeterminesFiberSpectrum ∧
      D.fiberSpectrumDeterminesMomentsAndSchur := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, D.signalRecurrence, pom_trivial_channel_finite_decidability_recoveredQ_eq D⟩
    intro n hn
    simpa [pom_trivial_channel_finite_decidability_convolutionCoefficient] using
      D.convolutionIdentity n hn
  · change D.fiberSpectrum =
      pom_trivial_channel_finite_decidability_decodeFiberSpectrum
        (List.ofFn
          fun i : Fin (D.order + 1) =>
            pom_trivial_channel_finite_decidability_recoveredQ D i.1)
    rw [pom_trivial_channel_finite_decidability_recoveredQ_eq D]
    exact D.fiberSpectrumFromCoefficients
  · refine ⟨?_, ?_⟩
    · intro q
      change
        pom_trivial_channel_finite_decidability_collisionMoment D.fiberSpectrum q =
          pom_trivial_channel_finite_decidability_collisionMoment
            (pom_trivial_channel_finite_decidability_decodeFiberSpectrum
              (List.ofFn
                fun i : Fin (D.order + 1) =>
                  pom_trivial_channel_finite_decidability_recoveredQ D i.1)) q
      rw [D.fiberSpectrumFromCoefficients]
      rw [pom_trivial_channel_finite_decidability_recoveredQ_eq D]
    · intro q
      change
        pom_trivial_channel_finite_decidability_schurChannelValue D.fiberSpectrum q =
          pom_trivial_channel_finite_decidability_schurChannelValue
            (pom_trivial_channel_finite_decidability_decodeFiberSpectrum
              (List.ofFn
                fun i : Fin (D.order + 1) =>
                  pom_trivial_channel_finite_decidability_recoveredQ D i.1)) q
      rw [D.fiberSpectrumFromCoefficients]
      rw [pom_trivial_channel_finite_decidability_recoveredQ_eq D]

end Omega.POM
