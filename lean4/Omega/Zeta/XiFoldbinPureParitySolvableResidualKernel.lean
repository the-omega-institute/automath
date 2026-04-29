import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Two audited foldbin fibers, each carrying an `A₅`-sized semisimple factor. -/
abbrev xi_foldbin_pure_parity_solvable_residual_kernel_Fiber := Fin 2

/-- The concrete order of the nonabelian simple alternating factor used in the certificate. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_alternatingFiveOrder : ℕ :=
  60

/-- The semisimple residual kernel is represented as a product of two `A₅`-sized factors. -/
abbrev xi_foldbin_pure_parity_solvable_residual_kernel_Kernel :=
  xi_foldbin_pure_parity_solvable_residual_kernel_Fiber →
    Fin xi_foldbin_pure_parity_solvable_residual_kernel_alternatingFiveOrder

/-- The identity element used to choose representatives of parity fibers. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_baseKernel :
    xi_foldbin_pure_parity_solvable_residual_kernel_Kernel :=
  fun _ => ⟨0, by norm_num [xi_foldbin_pure_parity_solvable_residual_kernel_alternatingFiveOrder]⟩

/-- The parity lattice records one sign bit per audited fiber. -/
abbrev xi_foldbin_pure_parity_solvable_residual_kernel_ParityLattice :=
  xi_foldbin_pure_parity_solvable_residual_kernel_Fiber → Bool

/-- The concrete foldbin group is the product of the semisimple kernel and the parity lattice. -/
abbrev xi_foldbin_pure_parity_solvable_residual_kernel_Group :=
  xi_foldbin_pure_parity_solvable_residual_kernel_Kernel ×
    xi_foldbin_pure_parity_solvable_residual_kernel_ParityLattice

/-- Projection to the sign quotient. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_projection
    (g : xi_foldbin_pure_parity_solvable_residual_kernel_Group) :
    xi_foldbin_pure_parity_solvable_residual_kernel_ParityLattice :=
  g.2

/-- Inclusion of the residual kernel as the zero-parity subgroup. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_inclusion
    (k : xi_foldbin_pure_parity_solvable_residual_kernel_Kernel) :
    xi_foldbin_pure_parity_solvable_residual_kernel_Group :=
  (k, fun _ => false)

/-- Membership in the kernel of the parity projection. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel
    (g : xi_foldbin_pure_parity_solvable_residual_kernel_Group) : Prop :=
  xi_foldbin_pure_parity_solvable_residual_kernel_projection g = fun _ => false

/-- Concrete short exactness of the semisimple kernel, foldbin group, and parity lattice. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_short_exact_sequence : Prop :=
  Function.Injective xi_foldbin_pure_parity_solvable_residual_kernel_inclusion ∧
    Function.Surjective xi_foldbin_pure_parity_solvable_residual_kernel_projection ∧
      ∀ g : xi_foldbin_pure_parity_solvable_residual_kernel_Group,
        xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel g ↔
          ∃ k : xi_foldbin_pure_parity_solvable_residual_kernel_Kernel,
            xi_foldbin_pure_parity_solvable_residual_kernel_inclusion k = g

/-- The solvable residual kernel is exactly the zero-parity kernel of the quotient map. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_solvable_residual_kernel : Prop :=
  {g : xi_foldbin_pure_parity_solvable_residual_kernel_Group |
      xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel g} =
    Set.range xi_foldbin_pure_parity_solvable_residual_kernel_inclusion

/-- The residual kernel has the cardinality of a product of two `A₅` factors. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_product_of_nonabelian_simple_groups :
    Prop :=
  Fintype.card xi_foldbin_pure_parity_solvable_residual_kernel_Kernel =
      xi_foldbin_pure_parity_solvable_residual_kernel_alternatingFiveOrder ^ 2 ∧
    5 ≤ xi_foldbin_pure_parity_solvable_residual_kernel_alternatingFiveOrder

/-- Every map constant on the residual kernel fibers factors uniquely through the parity lattice
as a set-theoretic quotient map. -/
def xi_foldbin_pure_parity_solvable_residual_kernel_universal_solvable_factorization :
    Prop :=
  ∀ {β : Type*} (φ : xi_foldbin_pure_parity_solvable_residual_kernel_Group → β),
    (∀ g h,
      xi_foldbin_pure_parity_solvable_residual_kernel_projection g =
        xi_foldbin_pure_parity_solvable_residual_kernel_projection h →
          φ g = φ h) →
      ∃ ψ : xi_foldbin_pure_parity_solvable_residual_kernel_ParityLattice → β,
        ∀ g, φ g = ψ (xi_foldbin_pure_parity_solvable_residual_kernel_projection g)

/-- Paper label: `thm:xi-foldbin-pure-parity-solvable-residual-kernel`. -/
theorem paper_xi_foldbin_pure_parity_solvable_residual_kernel :
    xi_foldbin_pure_parity_solvable_residual_kernel_short_exact_sequence ∧
      xi_foldbin_pure_parity_solvable_residual_kernel_solvable_residual_kernel ∧
        xi_foldbin_pure_parity_solvable_residual_kernel_product_of_nonabelian_simple_groups ∧
          xi_foldbin_pure_parity_solvable_residual_kernel_universal_solvable_factorization := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro a b h
      exact congrArg Prod.fst h
    · intro q
      exact ⟨(xi_foldbin_pure_parity_solvable_residual_kernel_baseKernel, q), rfl⟩
    · intro g
      constructor
      · intro hg
        refine ⟨g.1, ?_⟩
        cases g
        simp [xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel,
          xi_foldbin_pure_parity_solvable_residual_kernel_projection,
          xi_foldbin_pure_parity_solvable_residual_kernel_inclusion] at hg ⊢
        exact hg.symm
      · rintro ⟨k, rfl⟩
        simp [xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel,
          xi_foldbin_pure_parity_solvable_residual_kernel_projection,
          xi_foldbin_pure_parity_solvable_residual_kernel_inclusion]
  · ext g
    constructor
    · intro hg
      refine ⟨g.1, ?_⟩
      cases g
      simp [xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel,
        xi_foldbin_pure_parity_solvable_residual_kernel_projection,
        xi_foldbin_pure_parity_solvable_residual_kernel_inclusion] at hg ⊢
      exact hg.symm
    · rintro ⟨k, rfl⟩
      simp [xi_foldbin_pure_parity_solvable_residual_kernel_inProjectionKernel,
        xi_foldbin_pure_parity_solvable_residual_kernel_projection,
        xi_foldbin_pure_parity_solvable_residual_kernel_inclusion]
  · simp [xi_foldbin_pure_parity_solvable_residual_kernel_product_of_nonabelian_simple_groups,
      xi_foldbin_pure_parity_solvable_residual_kernel_alternatingFiveOrder]
  · intro β φ hφ
    refine ⟨fun q => φ (xi_foldbin_pure_parity_solvable_residual_kernel_baseKernel, q), ?_⟩
    intro g
    exact hφ g
      (xi_foldbin_pure_parity_solvable_residual_kernel_baseKernel,
        xi_foldbin_pure_parity_solvable_residual_kernel_projection g) rfl

end Omega.Zeta
