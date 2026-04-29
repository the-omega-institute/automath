import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Concrete finite-band package for the Lissajous cyclic-orbit alias computation. -/
structure xi_lissajous_cyclic_orbit_alias_lattice_data where
  xi_lissajous_cyclic_orbit_alias_lattice_N : ℕ
  xi_lissajous_cyclic_orbit_alias_lattice_hN :
    0 < xi_lissajous_cyclic_orbit_alias_lattice_N
  xi_lissajous_cyclic_orbit_alias_lattice_band : Finset ℤ
  xi_lissajous_cyclic_orbit_alias_lattice_coeff : ℤ → ℂ
  xi_lissajous_cyclic_orbit_alias_lattice_zero_mem :
    (0 : ℤ) ∈ xi_lissajous_cyclic_orbit_alias_lattice_band
  xi_lissajous_cyclic_orbit_alias_lattice_zero_kernel :
    ∀ m ∈ xi_lissajous_cyclic_orbit_alias_lattice_band,
      (m : ZMod xi_lissajous_cyclic_orbit_alias_lattice_N) = 0 → m = 0
  xi_lissajous_cyclic_orbit_alias_lattice_band_injective :
    Set.InjOn
      (fun m : ℤ => (m : ZMod xi_lissajous_cyclic_orbit_alias_lattice_N))
      {m : ℤ | m ∈ xi_lissajous_cyclic_orbit_alias_lattice_band}

namespace xi_lissajous_cyclic_orbit_alias_lattice_data

def xi_lissajous_cyclic_orbit_alias_lattice_kernel
    (D : xi_lissajous_cyclic_orbit_alias_lattice_data)
    (r : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) (m : ℤ) : ℂ :=
  if (m : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) = r then 1 else 0

def xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient
    (D : xi_lissajous_cyclic_orbit_alias_lattice_data)
    (r : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) : ℂ :=
  (D.xi_lissajous_cyclic_orbit_alias_lattice_band.filter fun m : ℤ =>
    (m : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) = r).sum
      D.xi_lissajous_cyclic_orbit_alias_lattice_coeff

def xi_lissajous_cyclic_orbit_alias_lattice_finiteAverage
    (D : xi_lissajous_cyclic_orbit_alias_lattice_data)
    (r : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) : ℂ :=
  D.xi_lissajous_cyclic_orbit_alias_lattice_band.sum fun m =>
    D.xi_lissajous_cyclic_orbit_alias_lattice_coeff m *
      D.xi_lissajous_cyclic_orbit_alias_lattice_kernel r m

def cyclicOrbit (D : xi_lissajous_cyclic_orbit_alias_lattice_data) : Prop :=
  ∀ k : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N,
    k + (D.xi_lissajous_cyclic_orbit_alias_lattice_N :
      ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) = k

def aliasDecomposition (D : xi_lissajous_cyclic_orbit_alias_lattice_data) : Prop :=
  ∀ r : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N,
    D.xi_lissajous_cyclic_orbit_alias_lattice_finiteAverage r =
      D.xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient r

def zeroFrequencyFormula (D : xi_lissajous_cyclic_orbit_alias_lattice_data) : Prop :=
  D.xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient 0 =
    (D.xi_lissajous_cyclic_orbit_alias_lattice_band.filter fun m : ℤ =>
      (m : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) = 0).sum
        D.xi_lissajous_cyclic_orbit_alias_lattice_coeff

def noAliasConstantRecovery (D : xi_lissajous_cyclic_orbit_alias_lattice_data) : Prop :=
  D.xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient 0 =
    D.xi_lissajous_cyclic_orbit_alias_lattice_coeff 0

def injectiveBandRecovery (D : xi_lissajous_cyclic_orbit_alias_lattice_data) : Prop :=
  ∀ m ∈ D.xi_lissajous_cyclic_orbit_alias_lattice_band,
    D.xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient
        (m : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) =
      D.xi_lissajous_cyclic_orbit_alias_lattice_coeff m

private theorem xi_lissajous_cyclic_orbit_alias_lattice_filter_singleton_zero
    (D : xi_lissajous_cyclic_orbit_alias_lattice_data) :
    (D.xi_lissajous_cyclic_orbit_alias_lattice_band.filter fun m : ℤ =>
      (m : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) = 0) = {0} := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hm
    exact D.xi_lissajous_cyclic_orbit_alias_lattice_zero_kernel m hm.1 hm.2
  · intro hm
    subst m
    exact ⟨D.xi_lissajous_cyclic_orbit_alias_lattice_zero_mem, by simp⟩

private theorem xi_lissajous_cyclic_orbit_alias_lattice_filter_singleton_band
    (D : xi_lissajous_cyclic_orbit_alias_lattice_data)
    {m : ℤ} (hm : m ∈ D.xi_lissajous_cyclic_orbit_alias_lattice_band) :
    (D.xi_lissajous_cyclic_orbit_alias_lattice_band.filter fun n : ℤ =>
      (n : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N) =
        (m : ZMod D.xi_lissajous_cyclic_orbit_alias_lattice_N)) = {m} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hn
    exact D.xi_lissajous_cyclic_orbit_alias_lattice_band_injective hn.1 hm hn.2
  · intro hn
    subst n
    exact ⟨hm, rfl⟩

end xi_lissajous_cyclic_orbit_alias_lattice_data

open xi_lissajous_cyclic_orbit_alias_lattice_data

/-- Paper label: `prop:xi-lissajous-cyclic-orbit-alias-lattice`. -/
theorem paper_xi_lissajous_cyclic_orbit_alias_lattice
    (D : xi_lissajous_cyclic_orbit_alias_lattice_data) :
    D.cyclicOrbit ∧ D.aliasDecomposition ∧ D.zeroFrequencyFormula ∧
      D.noAliasConstantRecovery ∧ D.injectiveBandRecovery := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simp
  · intro r
    simp [xi_lissajous_cyclic_orbit_alias_lattice_finiteAverage,
      xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient,
      xi_lissajous_cyclic_orbit_alias_lattice_kernel, Finset.sum_filter]
  · rw [zeroFrequencyFormula, xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient]
  · rw [noAliasConstantRecovery]
    simp [xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient,
      xi_lissajous_cyclic_orbit_alias_lattice_filter_singleton_zero D]
  · intro m hm
    simp [xi_lissajous_cyclic_orbit_alias_lattice_aliasCoefficient,
      xi_lissajous_cyclic_orbit_alias_lattice_filter_singleton_band D hm]

end

end Omega.Zeta
