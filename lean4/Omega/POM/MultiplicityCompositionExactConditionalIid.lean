import Mathlib

open scoped BigOperators

namespace Omega.POM

/-- Block weight `F_{k+2}^q` for the finite Fibonacci composition model. -/
def pomBlockWeight (q k : ℕ) : ℝ :=
  (Nat.fib (k + 2) : ℝ) ^ q

/-- Weight of an ordered composition path. -/
def pomCompositionWeight (q : ℕ) (path : List ℕ) : ℝ :=
  (path.map (pomBlockWeight q)).prod

/-- Finite partition function restricted to a prescribed family of length-`L` compositions. -/
def pomPartitionFunction (q : ℕ) (paths : Finset (List ℕ)) : ℝ :=
  paths.sum fun path => pomCompositionWeight q path

lemma pomCompositionProbability_factorization (q : ℕ) (rho : ℝ) :
    ∀ path : List ℕ,
      (path.map (fun k => pomBlockWeight q k * rho ^ k)).prod =
        pomCompositionWeight q path * rho ^ path.sum
  | [] => by simp [pomCompositionWeight]
  | k :: path => by
      rw [List.map_cons, List.prod_cons, pomCompositionWeight, List.map_cons, List.prod_cons,
        List.sum_cons, pow_add, pomCompositionProbability_factorization]
      rw [pomCompositionWeight]
      ring

/-- Finite-data wrapper for the exact conditional i.i.d. representation of weighted compositions.
The data specify a finite composition family, the i.i.d. step law, path probabilities, and the
conditioned law on the hitting event. -/
structure PomMultiplicityCompositionExactConditionalIidData where
  q : ℕ
  rho : ℝ
  L : ℕ
  paths : Finset (List ℕ)
  stepLaw : ℕ → ℝ
  pathProb : List ℕ → ℝ
  condProb : List ℕ → ℝ
  rho_ne_zero : rho ≠ 0
  path_sum : ∀ {path : List ℕ}, path ∈ paths → path.sum = L
  stepLaw_eq : ∀ k : ℕ, stepLaw k = pomBlockWeight q k * rho ^ k
  pathProb_eq : ∀ {path : List ℕ}, path ∈ paths → pathProb path = (path.map stepLaw).prod
  condProb_eq :
    ∀ {path : List ℕ}, path ∈ paths →
      (paths.sum fun path' => pathProb path') * condProb path = pathProb path

/-- The exact conditional i.i.d. conclusion: path probabilities factorize into the paper weight
times `ρ^L`, summing over all length-`L` compositions gives the hitting probability, and after
conditioning the common factor cancels to recover the composition weight. -/
def PomMultiplicityCompositionExactConditionalIidData.exactConditionalIid
    (D : PomMultiplicityCompositionExactConditionalIidData) : Prop :=
  (∀ path ∈ D.paths, D.pathProb path = pomCompositionWeight D.q path * D.rho ^ D.L) ∧
    (D.paths.sum fun path => D.pathProb path) = D.rho ^ D.L * pomPartitionFunction D.q D.paths ∧
    (∀ path ∈ D.paths, pomPartitionFunction D.q D.paths * D.condProb path =
      pomCompositionWeight D.q path)

/-- The finite hitting law of the i.i.d. renewal representation matches the weighted composition
law exactly after conditioning.
    thm:pom-multiplicity-composition-exact-conditional-iid -/
theorem paper_pom_multiplicity_composition_exact_conditional_iid
    (D : PomMultiplicityCompositionExactConditionalIidData) : D.exactConditionalIid := by
  have hPathProb :
      ∀ path ∈ D.paths, D.pathProb path = pomCompositionWeight D.q path * D.rho ^ D.L := by
    intro path hpath
    rw [D.pathProb_eq hpath]
    rw [show path.map D.stepLaw = path.map (fun k => pomBlockWeight D.q k * D.rho ^ k) by
      simp [D.stepLaw_eq]]
    rw [pomCompositionProbability_factorization, D.path_sum hpath]
  have hHit :
      (D.paths.sum fun path => D.pathProb path) = D.rho ^ D.L * pomPartitionFunction D.q D.paths := by
    calc
      D.paths.sum (fun path => D.pathProb path) =
          D.paths.sum (fun path => pomCompositionWeight D.q path * D.rho ^ D.L) := by
            refine Finset.sum_congr rfl ?_
            intro path hpath
            exact hPathProb path hpath
      _ = D.paths.sum (fun path => D.rho ^ D.L * pomCompositionWeight D.q path) := by
        refine Finset.sum_congr rfl ?_
        intro path hpath
        ring
      _ = D.rho ^ D.L * pomPartitionFunction D.q D.paths := by
        simp [pomPartitionFunction, Finset.mul_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro path hpath
    exact hPathProb path hpath
  · exact hHit
  · intro path hpath
    have hCond := D.condProb_eq hpath
    rw [hHit] at hCond
    rw [hPathProb path hpath] at hCond
    have hrhoL_ne : D.rho ^ D.L ≠ 0 := pow_ne_zero D.L D.rho_ne_zero
    have hCancel :
        (pomPartitionFunction D.q D.paths * D.condProb path) * D.rho ^ D.L =
          pomCompositionWeight D.q path * D.rho ^ D.L := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hCond
    exact mul_right_cancel₀ hrhoL_ne hCancel

end Omega.POM
