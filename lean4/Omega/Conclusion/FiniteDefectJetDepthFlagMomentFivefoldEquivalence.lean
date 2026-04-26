import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-defect-jet-depth-flag-moment-fivefold-equivalence`. -/
theorem paper_conclusion_finite_defect_jet_depth_flag_moment_fivefold_equivalence
    {ν : Type} {Jet Local Depth Moments Fingerprint : Type} (jet : ν -> Jet)
    («local» : ν -> Local) (depth : ν -> Depth) (moments : ν -> Moments)
    (fingerprint : ν -> Fingerprint) :
    (∀ a b, jet a = jet b ↔ «local» a = «local» b) ->
      (∀ a b, «local» a = «local» b ↔ depth a = depth b) ->
      (∀ a b, «local» a = «local» b ↔ fingerprint a = fingerprint b) ->
      (∀ a b, moments a = moments b ↔ fingerprint a = fingerprint b) ->
      ∀ a b, jet a = jet b ↔
        «local» a = «local» b ∧
          depth a = depth b ∧ moments a = moments b ∧ fingerprint a = fingerprint b := by
  intro hJetLocal hLocalDepth hLocalFingerprint hMomentsFingerprint a b
  constructor
  · intro hJet
    have hLocal : «local» a = «local» b := (hJetLocal a b).1 hJet
    have hDepth : depth a = depth b := (hLocalDepth a b).1 hLocal
    have hFingerprint : fingerprint a = fingerprint b := (hLocalFingerprint a b).1 hLocal
    have hMoments : moments a = moments b := (hMomentsFingerprint a b).2 hFingerprint
    exact ⟨hLocal, hDepth, hMoments, hFingerprint⟩
  · rintro ⟨hLocal, _, _, _⟩
    exact (hJetLocal a b).2 hLocal

end Omega.Conclusion
