import Mathlib.Tactic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.AddCircle.Defs

namespace Omega.Conclusion

open Set Topology

/-- A concrete finite-dimensional torus model. -/
abbrev UnitAddCircle := AddCircle (1 : ℝ)

/-- A concrete finite-dimensional torus model. -/
abbrev FiniteDimensionalTorus (d : ℕ) := Fin d → UnitAddCircle

private theorem continuous_hom_connected_to_totally_disconnected_zero
    {K P : Type*} [AddCommGroup K] [TopologicalSpace K] [ConnectedSpace K]
    [AddCommGroup P] [TopologicalSpace P] [TotallyDisconnectedSpace P]
    (f : K →+ P) (hf : Continuous f) :
    ∀ x : K, f x = 0 := by
  intro x
  have hconst : f x = f 0 :=
    TotallyDisconnectedSpace.eq_of_continuous (f : K → P) hf x 0
  simpa [hconst] using f.map_zero

private theorem finite_range_to_torus_of_bounded_exponent
    {P : Type*} [AddCommGroup P] (d n : ℕ) (hn : 0 < n)
    (hPtors : ∀ x : P, n • x = 0) (f : P →+ FiniteDimensionalTorus d) :
    (Set.range f).Finite := by
  let g : Set.range f → Fin d → {u : UnitAddCircle | n • u = 0} :=
    fun y i =>
      let x : P := Classical.choose y.2
      let hx : f x = y.1 := Classical.choose_spec y.2
      ⟨y.1 i, by
        rw [← hx]
        have hmap := congrArg (fun z : FiniteDimensionalTorus d => z i) (map_nsmul f n x)
        simpa [hPtors x] using hmap.symm⟩
  have hg : Function.Injective g := by
    intro y z h
    apply Subtype.ext
    funext i
    simpa [g] using congrArg Subtype.val (congrFun h i)
  haveI : Fintype {u : UnitAddCircle | n • u = 0} :=
    (AddCircle.finite_torsion (p := (1 : ℝ)) hn).fintype
  let _ : Finite (Set.range f) := Finite.of_injective g hg
  exact Set.toFinite _

/-- Paper label: `prop:conclusion-connected-profinite-orthogonality`. In the concrete bounded
exponent profinite-torsion model, connected phases map trivially to totally disconnected targets,
every torus-valued homomorphism has finite image, and therefore no infinite bounded-exponent
profinite axis can inject continuously into a finite-dimensional torus. -/
theorem paper_conclusion_connected_profinite_orthogonality
    (K P : Type*) [AddCommGroup K] [TopologicalSpace K] [ConnectedSpace K]
    [AddCommGroup P] [TopologicalSpace P] [TotallyDisconnectedSpace P]
    (d n : ℕ) (hn : 0 < n) (hPtors : ∀ x : P, n • x = 0) [Infinite P] :
    (∀ f : K →+ P, Continuous f → ∀ x : K, f x = 0) ∧
      (∀ f : P →+ FiniteDimensionalTorus d, Continuous f → (Set.range f).Finite) ∧
      ¬ ∃ f : P →+ FiniteDimensionalTorus d, Continuous f ∧ Function.Injective f := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    exact continuous_hom_connected_to_totally_disconnected_zero f hf
  · intro f _
    exact finite_range_to_torus_of_bounded_exponent d n hn hPtors f
  · rintro ⟨f, hf, hfinj⟩
    have hfinite : (Set.range f).Finite :=
      finite_range_to_torus_of_bounded_exponent d n hn hPtors f
    have hinfinite : (Set.range f).Infinite := by
      exact (infinite_range_iff hfinj).2 inferInstance
    exact hfinite.not_infinite hinfinite

end Omega.Conclusion
