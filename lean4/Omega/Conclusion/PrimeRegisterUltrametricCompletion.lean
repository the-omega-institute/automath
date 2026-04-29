import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Conclusion.RegisterUltrametricLipschitzAndGodelNoRealExtension

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Cauchy sequences for the prefix-ultrametric uniformity. -/
def registerCauchy (u : ℕ → RegisterStream) : Prop :=
  ∀ k, ∃ N, ∀ m ≥ N, ∀ n ≥ N, prefixAgree k (u m) (u n)

/-- Coordinatewise eventual stabilization, which is equivalent to Cauchy for the prefix
ultrametric. -/
def coordinatewiseEventuallyStable (u : ℕ → RegisterStream) : Prop :=
  ∀ t, ∃ N, ∀ n ≥ N, u n t = u N t

/-- Convergence in the prefix-ultrametric uniformity. -/
def convergesTo (u : ℕ → RegisterStream) (r : RegisterStream) : Prop :=
  ∀ k, ∃ N, ∀ n ≥ N, prefixAgree k (u n) r

/-- Strong triangle inequality phrased on prefix balls: if `r` and `s` agree to depth `k`, and
`s` and `t` agree to depth `k`, then so do `r` and `t`. -/
def isUltrametric : Prop :=
  ∀ k r s t, prefixAgree k r s → prefixAgree k s t → prefixAgree k r t

/-- The completion statement used in this file: every prefix-Cauchy sequence converges to a full
register stream. -/
def completion_eq_fullRegisterProduct : Prop :=
  ∀ u, registerCauchy u → ∃ r : RegisterStream, convergesTo u r

/-- Finite-support prime-register streams. -/
def finiteSupport (r : RegisterStream) : Prop :=
  ∃ N, ∀ t ≥ N, r t = 0

/-- Truncation to the first `N` prime coordinates. -/
def truncateRegister (N : ℕ) (r : RegisterStream) : RegisterStream :=
  fun t => if t < N then r t else 0

/-- Continuity for the prefix-ultrametric: output agreement to depth `k` follows from sufficiently
deep input agreement. -/
def prefixContinuous (F : RegisterStream → RegisterStream) : Prop :=
  ∀ r k, ∃ N, ∀ s, prefixAgree N s r → prefixAgree k (F s) (F r)

/-- The coordinatewise Gödel-value extension, implemented on the completion as the identity map on
the full prime-register product. -/
def godelValueExtension : RegisterStream → RegisterStream := id

/-- Agreement with the finite-support Gödel coding on the dense finite-support subspace. -/
def extendsFiniteSupportIdentity (F : RegisterStream → RegisterStream) : Prop :=
  ∀ r, finiteSupport r → F r = r

/-- The finite-support Gödel map extends continuously and uniquely to the full prime-register
product. -/
def godelValue_hasUniqueContinuousExtension : Prop :=
  prefixContinuous godelValueExtension ∧
    ∀ F, prefixContinuous F → extendsFiniteSupportIdentity F → F = godelValueExtension

/-- A chosen stabilization index for coordinate `t`. -/
def stabilizationIndex (u : ℕ → RegisterStream) (hstable : coordinatewiseEventuallyStable u) (t : ℕ) :
    ℕ :=
  Classical.choose (hstable t)

lemma stabilizationIndex_spec (u : ℕ → RegisterStream) (hstable : coordinatewiseEventuallyStable u)
    (t n : ℕ) (hn : stabilizationIndex u hstable t ≤ n) :
    u n t = u (stabilizationIndex u hstable t) t :=
  Classical.choose_spec (hstable t) n hn

lemma isUltrametric_holds : isUltrametric := by
  intro k r s t hrs hst u hu
  rw [hrs u hu, hst u hu]

lemma registerCauchy_iff_coordinatewiseEventuallyStable (u : ℕ → RegisterStream) :
    registerCauchy u ↔ coordinatewiseEventuallyStable u := by
  constructor
  · intro hcauchy t
    rcases hcauchy (t + 1) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact (hN N (le_rfl) n hn t (Nat.lt_succ_self t)).symm
  · intro hstable k
    refine ⟨(Finset.range k).sup fun t => stabilizationIndex u hstable t, ?_⟩
    intro m hm n hn t ht
    have htm : stabilizationIndex u hstable t ≤
        (Finset.range k).sup fun s => stabilizationIndex u hstable s := by
      exact Finset.le_sup (Finset.mem_range.mpr ht)
    have hm' : stabilizationIndex u hstable t ≤ m := le_trans htm hm
    have hn' : stabilizationIndex u hstable t ≤ n := le_trans htm hn
    calc
      u m t = u (stabilizationIndex u hstable t) t := stabilizationIndex_spec u hstable t m hm'
      _ = u n t := (stabilizationIndex_spec u hstable t n hn').symm

/-- The stabilized value of a Cauchy sequence at coordinate `t`. -/
def stabilizedLimit (u : ℕ → RegisterStream) (hstable : coordinatewiseEventuallyStable u) :
    RegisterStream :=
  fun t => u (stabilizationIndex u hstable t) t

lemma truncateRegister_finiteSupport (N : ℕ) (r : RegisterStream) :
    finiteSupport (truncateRegister N r) := by
  refine ⟨N, ?_⟩
  intro t ht
  simp [truncateRegister, not_lt_of_ge ht]

lemma prefixAgree_truncate (N : ℕ) (r : RegisterStream) :
    prefixAgree N (truncateRegister N r) r := by
  intro t ht
  simp [truncateRegister, ht]

lemma stabilizedLimit_converges (u : ℕ → RegisterStream)
    (hstable : coordinatewiseEventuallyStable u) :
    convergesTo u (stabilizedLimit u hstable) := by
  intro k
  refine ⟨(Finset.range k).sup fun t => stabilizationIndex u hstable t, ?_⟩
  intro n hn t ht
  have htbound : stabilizationIndex u hstable t ≤
      (Finset.range k).sup fun s => stabilizationIndex u hstable s := by
    exact Finset.le_sup (Finset.mem_range.mpr ht)
  have hn' : stabilizationIndex u hstable t ≤ n := le_trans htbound hn
  exact stabilizationIndex_spec u hstable t n hn'

lemma completion_eq_fullRegisterProduct_holds : completion_eq_fullRegisterProduct := by
  intro u hcauchy
  have hstable : coordinatewiseEventuallyStable u :=
    (registerCauchy_iff_coordinatewiseEventuallyStable u).1 hcauchy
  exact ⟨stabilizedLimit u hstable, stabilizedLimit_converges u hstable⟩

lemma prefixContinuous_godelValueExtension : prefixContinuous godelValueExtension := by
  intro r k
  refine ⟨k, ?_⟩
  intro s hs
  simpa [godelValueExtension] using hs

lemma unique_extension_of_prefixContinuous (F : RegisterStream → RegisterStream)
    (hcont : prefixContinuous F) (hext : extendsFiniteSupportIdentity F) :
    F = godelValueExtension := by
  funext r
  ext t
  rcases hcont r (t + 1) with ⟨M, hM⟩
  let N := max M (t + 1)
  have hinput : prefixAgree M (truncateRegister N r) r := by
    intro u hu
    have huN : u < N := lt_of_lt_of_le hu (Nat.le_max_left _ _)
    simp [truncateRegister, huN]
  have houtput : prefixAgree (t + 1) (F (truncateRegister N r)) (F r) := hM _ hinput
  have htruncFix : F (truncateRegister N r) = truncateRegister N r := by
    exact hext _ (truncateRegister_finiteSupport N r)
  have htruncAgree : prefixAgree (t + 1) (truncateRegister N r) r := by
    intro u hu
    have huN : u < N := lt_of_lt_of_le hu (Nat.le_max_right _ _)
    simp [truncateRegister, huN]
  calc
    F r t = F (truncateRegister N r) t := by
      symm
      exact houtput t (Nat.lt_succ_self t)
    _ = truncateRegister N r t := by rw [htruncFix]
    _ = r t := htruncAgree t (Nat.lt_succ_self t)

/-- Paper label: `thm:conclusion-prime-register-ultrametric-completion`.
The prefix ultrametric is ultrametric in the strong sense, its completion is the full product of
prime-register coordinates, and the finite-support Gödel coding has a unique continuous
coordinatewise extension. -/
theorem paper_conclusion_prime_register_ultrametric_completion :
    isUltrametric ∧ completion_eq_fullRegisterProduct ∧
      godelValue_hasUniqueContinuousExtension := by
  refine ⟨isUltrametric_holds, completion_eq_fullRegisterProduct_holds, ?_⟩
  refine ⟨prefixContinuous_godelValueExtension, ?_⟩
  intro F hcont hext
  exact unique_extension_of_prefixContinuous F hcont hext

end

end Omega.Conclusion
