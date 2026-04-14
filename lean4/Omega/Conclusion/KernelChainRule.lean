import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Omega.Conclusion

/-- Chain rule for kernel ranks: for composable linear maps f : M →ₗ[R] N and g : N →ₗ[R] P,
    finrank(ker(g ∘ f)) = finrank(ker f) + finrank(ker(g|_{range f})).
    thm:conclusion-finite-rank-kernel-chain-rule -/
theorem kernel_chain_rank_add {R : Type*} [CommRing R] [IsDomain R]
    {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Module.finrank R (LinearMap.ker (g ∘ₗ f)) =
      Module.finrank R (LinearMap.ker f) +
      Module.finrank R (LinearMap.ker (g.domRestrict (LinearMap.range f))) := by
  set K := LinearMap.ker (g ∘ₗ f)
  set Kf := LinearMap.ker f
  set Kgr := LinearMap.ker (g.domRestrict (LinearMap.range f))
  -- Build the map φ : K →ₗ[R] Kgr sending x to ⟨f(x), mem_range⟩
  let φ : K →ₗ[R] Kgr := LinearMap.codRestrict Kgr
    (LinearMap.codRestrict (LinearMap.range f) (f.comp K.subtype) (fun ⟨_, _⟩ => ⟨_, rfl⟩))
    (fun ⟨x, hx⟩ => by
      simp only [Kgr, LinearMap.mem_ker, LinearMap.domRestrict_apply,
        LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      exact hx)
  -- ker φ = ker f (inside K)
  have hker_φ : LinearMap.ker φ = Kf.comap K.subtype := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Kf]
    constructor
    · intro h
      -- φ ⟨x, hx⟩ = 0 means f x = 0 in range f
      have h1 : (φ ⟨x, hx⟩ : Kgr).1 = (0 : LinearMap.range f) :=
        congr_arg Subtype.val h
      have h2 : ((φ ⟨x, hx⟩ : Kgr).1 : N) = (0 : N) := congr_arg Subtype.val h1
      simpa [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.subtype_apply] using h2
    · intro (h : f x = 0)
      apply Subtype.ext; apply Subtype.ext
      simp [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply, h]
  -- φ is surjective
  have hsurj : Function.Surjective φ := by
    intro ⟨⟨y, x, hfx⟩, (hy : g y = 0)⟩
    exact ⟨⟨x, show g (f x) = 0 from hfx ▸ hy⟩, by
      apply Subtype.ext; apply Subtype.ext
      simp [φ, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, hfx]⟩
  -- Use cross-universe rank-nullity for φ : K →ₗ[R] Kgr
  have hrn := LinearMap.lift_rank_eq_of_surjective hsurj
  -- ker φ ≃ Kf via comapSubtypeEquivOfLe
  have hle : Kf ≤ K := LinearMap.ker_le_ker_comp f g
  have hcomap_rank : Module.rank R (Kf.comap K.subtype) = Module.rank R Kf :=
    (Submodule.comapSubtypeEquivOfLe hle).rank_eq
  rw [hker_φ, hcomap_rank] at hrn
  -- hrn : lift (rank K) = lift (rank Kgr) + lift (rank Kf)
  -- All ranks are < ℵ₀
  have hK_lt : Module.rank R K < Cardinal.aleph0 :=
    (Submodule.rank_le K).trans_lt (Module.rank_lt_aleph0 R M)
  have hKf_lt : Module.rank R Kf < Cardinal.aleph0 :=
    (Submodule.rank_le Kf).trans_lt (Module.rank_lt_aleph0 R M)
  have hKgr_lt : Module.rank R Kgr < Cardinal.aleph0 :=
    (Submodule.rank_le Kgr).trans_lt
      ((Submodule.rank_le (LinearMap.range f)).trans_lt (Module.rank_lt_aleph0 R N))
  -- Convert to finrank via toNat
  simp only [Module.finrank]
  -- Apply toNat to hrn (cross-universe equation)
  apply_fun Cardinal.toNat at hrn
  rw [Cardinal.toNat_lift] at hrn
  have hKgr_lift : Cardinal.lift.{u_2, u_3} (Module.rank R Kgr) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr hKgr_lt
  have hKf_lift : Cardinal.lift.{u_3, u_2} (Module.rank R Kf) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr hKf_lt
  rw [Cardinal.toNat_add hKgr_lift hKf_lift,
    Cardinal.toNat_lift, Cardinal.toNat_lift] at hrn
  omega

/-- Seed values for the kernel chain rule.
    thm:conclusion-finite-rank-kernel-chain-rule -/
theorem paper_conclusion_kernel_chain_rule_seeds :
    (∀ a _b : ℕ, a + 0 = a) ∧
    (∀ _a b : ℕ, 0 + b = b) ∧
    (1 + 0 = 1) := by
  exact ⟨fun a _ => Nat.add_zero a, fun _ b => Nat.zero_add b, rfl⟩

/-- Paper conclusion wrapper for the finite-rank kernel chain rule.
    thm:conclusion-finite-rank-kernel-chain-rule -/
theorem paper_conclusion_finite_rank_kernel_chain_rule
    {R : Type*} [CommRing R] [IsDomain R]
    {M N P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    Module.finrank R (LinearMap.ker (g ∘ₗ f)) =
      Module.finrank R (LinearMap.ker f) +
      Module.finrank R (LinearMap.ker (g.domRestrict (LinearMap.range f))) := by
  simpa using kernel_chain_rank_add f g

end Omega.Conclusion
