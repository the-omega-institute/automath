import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete length-two atom sampling model.  The primitive and core coordinates form the Nyquist
sample key; the hypotheses record length-two support, injectivity of the primitive/core interface,
and preservation of the torsion energy under sampling. -/
structure conclusion_length2_atom_nyquist_rigidity_data where
  conclusion_length2_atom_nyquist_rigidity_Atom : Type
  conclusion_length2_atom_nyquist_rigidity_length :
    conclusion_length2_atom_nyquist_rigidity_Atom → ℕ
  conclusion_length2_atom_nyquist_rigidity_primitive :
    conclusion_length2_atom_nyquist_rigidity_Atom → ℤ
  conclusion_length2_atom_nyquist_rigidity_core :
    conclusion_length2_atom_nyquist_rigidity_Atom → ℤ
  conclusion_length2_atom_nyquist_rigidity_energy :
    conclusion_length2_atom_nyquist_rigidity_Atom → ℝ
  conclusion_length2_atom_nyquist_rigidity_sampleEnergy : ℤ × ℤ → ℝ
  conclusion_length2_atom_nyquist_rigidity_length_two :
    ∀ a, conclusion_length2_atom_nyquist_rigidity_length a = 2
  conclusion_length2_atom_nyquist_rigidity_primitive_core_injective :
    ∀ {a b},
      conclusion_length2_atom_nyquist_rigidity_length a = 2 →
        conclusion_length2_atom_nyquist_rigidity_length b = 2 →
          conclusion_length2_atom_nyquist_rigidity_primitive a =
              conclusion_length2_atom_nyquist_rigidity_primitive b →
            conclusion_length2_atom_nyquist_rigidity_core a =
                conclusion_length2_atom_nyquist_rigidity_core b →
              a = b
  conclusion_length2_atom_nyquist_rigidity_energy_preserving :
    ∀ a,
      conclusion_length2_atom_nyquist_rigidity_sampleEnergy
          (conclusion_length2_atom_nyquist_rigidity_primitive a,
            conclusion_length2_atom_nyquist_rigidity_core a) =
        conclusion_length2_atom_nyquist_rigidity_energy a

namespace conclusion_length2_atom_nyquist_rigidity_data

/-- Nyquist sample key formed from the primitive and core generating-function coordinates. -/
def conclusion_length2_atom_nyquist_rigidity_sample
    (D : conclusion_length2_atom_nyquist_rigidity_data)
    (a : D.conclusion_length2_atom_nyquist_rigidity_Atom) : ℤ × ℤ :=
  (D.conclusion_length2_atom_nyquist_rigidity_primitive a,
    D.conclusion_length2_atom_nyquist_rigidity_core a)

/-- Local injectivity of length-two atoms under the Nyquist sample key. -/
def conclusion_length2_atom_nyquist_rigidity_local_injection
    (D : conclusion_length2_atom_nyquist_rigidity_data) : Prop :=
  ∀ a b,
    D.conclusion_length2_atom_nyquist_rigidity_sample a =
      D.conclusion_length2_atom_nyquist_rigidity_sample b →
    a = b

/-- Torsion energy is preserved by the primitive/core sample. -/
def conclusion_length2_atom_nyquist_rigidity_energy_identity
    (D : conclusion_length2_atom_nyquist_rigidity_data) : Prop :=
  ∀ a,
    D.conclusion_length2_atom_nyquist_rigidity_sampleEnergy
        (D.conclusion_length2_atom_nyquist_rigidity_sample a) =
      D.conclusion_length2_atom_nyquist_rigidity_energy a

/-- No-alias identity for the two-coordinate Nyquist sample. -/
def conclusion_length2_atom_nyquist_rigidity_no_alias
    (D : conclusion_length2_atom_nyquist_rigidity_data) : Prop :=
  ∀ a b,
    D.conclusion_length2_atom_nyquist_rigidity_sample a =
        D.conclusion_length2_atom_nyquist_rigidity_sample b ↔
      D.conclusion_length2_atom_nyquist_rigidity_primitive a =
          D.conclusion_length2_atom_nyquist_rigidity_primitive b ∧
        D.conclusion_length2_atom_nyquist_rigidity_core a =
          D.conclusion_length2_atom_nyquist_rigidity_core b

end conclusion_length2_atom_nyquist_rigidity_data

open conclusion_length2_atom_nyquist_rigidity_data

/-- Paper-facing conclusion for length-two atom Nyquist rigidity. -/
def conclusion_length2_atom_nyquist_rigidity_conclusion
    (D : conclusion_length2_atom_nyquist_rigidity_data) : Prop :=
  (∀ a, D.conclusion_length2_atom_nyquist_rigidity_length a = 2) ∧
    D.conclusion_length2_atom_nyquist_rigidity_local_injection ∧
      D.conclusion_length2_atom_nyquist_rigidity_energy_identity ∧
        D.conclusion_length2_atom_nyquist_rigidity_no_alias

lemma conclusion_length2_atom_nyquist_rigidity_local_injection_proof
    (D : conclusion_length2_atom_nyquist_rigidity_data) :
    D.conclusion_length2_atom_nyquist_rigidity_local_injection := by
  intro a b hsample
  apply D.conclusion_length2_atom_nyquist_rigidity_primitive_core_injective
      (D.conclusion_length2_atom_nyquist_rigidity_length_two a)
      (D.conclusion_length2_atom_nyquist_rigidity_length_two b)
  · exact congrArg Prod.fst hsample
  · exact congrArg Prod.snd hsample

lemma conclusion_length2_atom_nyquist_rigidity_energy_identity_proof
    (D : conclusion_length2_atom_nyquist_rigidity_data) :
    D.conclusion_length2_atom_nyquist_rigidity_energy_identity := by
  intro a
  simpa [conclusion_length2_atom_nyquist_rigidity_sample]
    using D.conclusion_length2_atom_nyquist_rigidity_energy_preserving a

lemma conclusion_length2_atom_nyquist_rigidity_no_alias_proof
    (D : conclusion_length2_atom_nyquist_rigidity_data) :
    D.conclusion_length2_atom_nyquist_rigidity_no_alias := by
  intro a b
  constructor
  · intro hsample
    exact ⟨congrArg Prod.fst hsample, congrArg Prod.snd hsample⟩
  · rintro ⟨hprimitive, hcore⟩
    simp [conclusion_length2_atom_nyquist_rigidity_sample, hprimitive, hcore]

/-- Paper label: `thm:conclusion-length2-atom-nyquist-rigidity`. -/
theorem paper_conclusion_length2_atom_nyquist_rigidity
    (D : conclusion_length2_atom_nyquist_rigidity_data) :
    conclusion_length2_atom_nyquist_rigidity_conclusion D := by
  exact ⟨D.conclusion_length2_atom_nyquist_rigidity_length_two,
    conclusion_length2_atom_nyquist_rigidity_local_injection_proof D,
    conclusion_length2_atom_nyquist_rigidity_energy_identity_proof D,
    conclusion_length2_atom_nyquist_rigidity_no_alias_proof D⟩

end Omega.Conclusion
