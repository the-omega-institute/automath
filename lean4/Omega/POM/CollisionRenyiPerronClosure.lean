import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.AddCollisionSpectrumRenyiMonotone
import Omega.POM.HankelFreeEnergyEvaluator
import Omega.POM.HankelRealizationProtocol

namespace Omega.POM

/-- Concrete data for the Perron-closure packaging of a collision Rényi moment sequence.  The
sample sequence is the finite-rank/Hankel readout, `perronRoot` is the spectral radius extracted
from the realization, and `renyiRate` records the normalized Rényi rates across moment orders. -/
structure pom_collision_renyi_perron_closure_data (q : Nat) where
  pom_collision_renyi_perron_closure_samples : Nat → ℝ
  pom_collision_renyi_perron_closure_perronRoot : ℝ
  pom_collision_renyi_perron_closure_renyiRate : Nat → ℝ
  pom_collision_renyi_perron_closure_endpointRate : ℝ
  pom_collision_renyi_perron_closure_perron_nonneg :
    0 ≤ pom_collision_renyi_perron_closure_perronRoot
  pom_collision_renyi_perron_closure_hankel_growth :
    ∀ m : Nat,
      pom_collision_renyi_perron_closure_samples m =
        pom_collision_renyi_perron_closure_perronRoot ^ m
  pom_collision_renyi_perron_closure_renyi_antitone :
    Antitone pom_collision_renyi_perron_closure_renyiRate
  pom_collision_renyi_perron_closure_endpoint_readout :
    pom_collision_renyi_perron_closure_endpointRate =
      sInf (Set.range pom_collision_renyi_perron_closure_renyiRate)

/-- The Hankel/Perron growth readout for the target sequence. -/
def pom_collision_renyi_perron_closure_growth {q : Nat}
    (D : pom_collision_renyi_perron_closure_data q) : Prop :=
  ∀ m : Nat,
    D.pom_collision_renyi_perron_closure_samples m =
      D.pom_collision_renyi_perron_closure_perronRoot ^ m

/-- The exact Perron readout makes the collision sequence multiplicative, hence submultiplicative,
and identifies the one-step exponential base. -/
def pom_collision_renyi_perron_closure_submultiplicative_limit {q : Nat}
    (D : pom_collision_renyi_perron_closure_data q) : Prop :=
  (∀ m n : Nat,
      D.pom_collision_renyi_perron_closure_samples (m + n) ≤
        D.pom_collision_renyi_perron_closure_samples m *
          D.pom_collision_renyi_perron_closure_samples n) ∧
    D.pom_collision_renyi_perron_closure_samples 1 =
      D.pom_collision_renyi_perron_closure_perronRoot

/-- Normalized Rényi rates are monotone in the moment order and have the recorded endpoint
readout. -/
def pom_collision_renyi_perron_closure_renyi_monotone {q : Nat}
    (D : pom_collision_renyi_perron_closure_data q) : Prop :=
  Antitone D.pom_collision_renyi_perron_closure_renyiRate ∧
    D.pom_collision_renyi_perron_closure_endpointRate =
      sInf (Set.range D.pom_collision_renyi_perron_closure_renyiRate)

/-- Paper label: `prop:pom-collision-renyi-perron-closure`. -/
theorem paper_pom_collision_renyi_perron_closure (q : Nat) (_hq : 2 ≤ q)
    (D : pom_collision_renyi_perron_closure_data q) :
    pom_collision_renyi_perron_closure_growth D ∧
      pom_collision_renyi_perron_closure_submultiplicative_limit D ∧
      pom_collision_renyi_perron_closure_renyi_monotone D := by
  refine ⟨D.pom_collision_renyi_perron_closure_hankel_growth, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro m n
      rw [D.pom_collision_renyi_perron_closure_hankel_growth (m + n),
        D.pom_collision_renyi_perron_closure_hankel_growth m,
        D.pom_collision_renyi_perron_closure_hankel_growth n]
      rw [pow_add]
    · simpa using D.pom_collision_renyi_perron_closure_hankel_growth 1
  · exact ⟨D.pom_collision_renyi_perron_closure_renyi_antitone,
      D.pom_collision_renyi_perron_closure_endpoint_readout⟩

end Omega.POM
