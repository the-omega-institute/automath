import Omega.Conclusion.LeyangS5TwoChannelMinimalCompleteness
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-rho5-wall-compression-codimension-one-residual`. -/
theorem paper_conclusion_leyang_rho5_wall_compression_codimension_one_residual
    (v : Omega.Conclusion.LeyangS5DensityVector) :
    ∃ line : ℚ → Omega.Conclusion.LeyangS5DensityVector,
      line 0 = v ∧
        (∀ t : ℚ,
          Omega.Conclusion.rho5Coordinates (line t) = Omega.Conclusion.rho5Coordinates v) ∧
        (∀ w,
          Omega.Conclusion.IsNormalizedDensity w →
            Omega.Conclusion.rho5Coordinates w = Omega.Conclusion.rho5Coordinates v →
              ∃ t : ℚ, w = line t) := by
  classical
  let qOfCode : ℕ → ℚ := fun k => (Encodable.decode (α := ℚ) k).getD 0
  let normalizedFiberPoint : ℚ → LeyangS5DensityVector := fun q i =>
    match i.1 with
    | 0 => 1 - (v 1 + v 2 + v 3 + v 4 + v 5 + v 6)
    | 1 => v 1 + v 2 - q
    | 2 => q
    | 3 => v 3
    | 4 => v 4
    | 5 => v 5
    | _ => v 6
  let line : ℚ → LeyangS5DensityVector := fun t =>
    if t = 0 then v
    else if h : ∃ n : ℕ, t = (n + 1 : ℚ) then
      normalizedFiberPoint (qOfCode (Classical.choose h))
    else
      normalizedFiberPoint 0
  refine ⟨line, ?_, ?_, ?_⟩
  · ext i
    simp [line]
  · intro t
    by_cases ht : t = 0
    · simp [line, ht]
    · by_cases hnat : ∃ n : ℕ, t = (n + 1 : ℚ)
      · simp [line, ht, hnat, rho5Coordinates, normalizedFiberPoint]
      · simp [line, ht, hnat, rho5Coordinates, normalizedFiberPoint]
  · intro w hw hρ
    let n : ℕ := Encodable.encode (w 2)
    let t : ℚ := (n + 1 : ℚ)
    have ht : t ≠ 0 := by
      dsimp [t]
      exact_mod_cast Nat.succ_ne_zero n
    have hnat : ∃ k : ℕ, t = (k + 1 : ℚ) := ⟨n, by simp [t]⟩
    have hchoose : Classical.choose hnat = n := by
      have hs : t = (Classical.choose hnat + 1 : ℚ) := Classical.choose_spec hnat
      have hs' : ((n + 1 : ℕ) : ℚ) = (Classical.choose hnat + 1 : ℚ) := by
        simpa [t] using hs
      have hsNat : n + 1 = Classical.choose hnat + 1 := by
        exact_mod_cast hs'
      omega
    have hqn : qOfCode n = w 2 := by
      dsimp [qOfCode, n]
      simp
    have h6 : w 6 = v 6 := by
      have h := congrArg (fun p : ℚ × ℚ × ℚ × ℚ × ℚ => p.1) hρ
      dsimp [rho5Coordinates] at h
      linarith
    have h5 : w 5 = v 5 := by
      have h := congrArg (fun p : ℚ × ℚ × ℚ × ℚ × ℚ => p.2.1) hρ
      dsimp [rho5Coordinates] at h
      linarith
    have h4 : w 4 = v 4 := by
      have h := congrArg (fun p : ℚ × ℚ × ℚ × ℚ × ℚ => p.2.2.1) hρ
      dsimp [rho5Coordinates] at h
      linarith
    have h3 : w 3 = v 3 := by
      have h := congrArg (fun p : ℚ × ℚ × ℚ × ℚ × ℚ => p.2.2.2.1) hρ
      dsimp [rho5Coordinates] at h
      linarith
    have h12 : w 1 + w 2 = v 1 + v 2 := by
      have h := congrArg (fun p : ℚ × ℚ × ℚ × ℚ × ℚ => p.2.2.2.2) hρ
      dsimp [rho5Coordinates] at h
      linarith
    have h0 : w 0 = 1 - (v 1 + v 2 + v 3 + v 4 + v 5 + v 6) := by
      dsimp [IsNormalizedDensity] at hw
      linarith
    refine ⟨t, ?_⟩
    ext i
    fin_cases i
    all_goals simp [line, ht, hnat, hchoose, normalizedFiberPoint, hqn, h0, h3, h4, h5, h6] <;>
      linarith

end Omega.Conclusion
