import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Zeta

/-- Seed notion of an arithmetic size that can be realized inside the `ZMod 21` dictionary model:
any ideal-size, additive-coset-size, ring-hom image-size, or fiber-size extracted from the
ambient cyclic ring must divide the ambient cardinality `21`. -/
def xi_time_part51aa_window6_root_dictionary_externality_internalizable_size (n : ℕ) : Prop :=
  n ∣ Fintype.card (ZMod 21)

/-- The audited `BC₃` root-data package contributes the incompatible cardinalities `18`, `6`,
and `12`; after transport to `ZMod 21`, the divisibility constraint on arithmetic sizes excludes
all three. -/
def xi_time_part51aa_window6_root_dictionary_externality_spec : Prop :=
  (Omega.GU.b3VisibleSupport.erase Omega.GU.zeroWeight).card = 18 ∧
    Fintype.card Omega.GU.Window6ShortRootParityBlock = 6 ∧
    Fintype.card Omega.GU.Window6LongRootParityBlock = 12 ∧
    (∀ _β : Fin 21 ≃ ZMod 21,
      ¬ xi_time_part51aa_window6_root_dictionary_externality_internalizable_size 18 ∧
        ¬ xi_time_part51aa_window6_root_dictionary_externality_internalizable_size 6 ∧
        ¬ xi_time_part51aa_window6_root_dictionary_externality_internalizable_size 12)

/-- Paper label: `thm:xi-time-part51aa-window6-root-dictionary-externality`. -/
theorem paper_xi_time_part51aa_window6_root_dictionary_externality :
    xi_time_part51aa_window6_root_dictionary_externality_spec := by
  rcases Omega.GU.paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨hb3, _hc3, _hBoundary, _hb3Adj, _hc3Adj, hshort, hlong, _hbdry, _hcoord, _hproj, _hsplit⟩
  refine ⟨hb3, hshort, hlong, ?_⟩
  intro _β
  constructor
  · intro h18
    have hcard : Fintype.card (ZMod 21) = 21 := by simp
    rw [xi_time_part51aa_window6_root_dictionary_externality_internalizable_size, hcard] at h18
    omega
  constructor
  · intro h6
    have hcard : Fintype.card (ZMod 21) = 21 := by simp
    rw [xi_time_part51aa_window6_root_dictionary_externality_internalizable_size, hcard] at h6
    omega
  · intro h12
    have hcard : Fintype.card (ZMod 21) = 21 := by simp
    rw [xi_time_part51aa_window6_root_dictionary_externality_internalizable_size, hcard] at h12
    omega

end Omega.Zeta
