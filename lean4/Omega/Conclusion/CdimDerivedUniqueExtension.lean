import Mathlib.Data.Int.Cast.Lemmas

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-cdim-derived-unique-extension`. -/
theorem paper_conclusion_cdim_derived_unique_extension (χ : ℤ → ℤ)
    (hadd : ∀ a b, χ (a + b) = χ a + χ b) (hZ : χ 1 = 1) :
    ∀ n : ℤ, χ n = n := by
  let χHom : ℤ →+ ℤ :=
    { toFun := χ
      map_zero' := by
        have h := hadd 0 0
        simp only [zero_add] at h
        omega
      map_add' := hadd }
  have hχHom : χHom = AddMonoidHom.id ℤ := by
    apply AddMonoidHom.ext_int
    simpa [χHom] using hZ
  intro n
  simpa [χHom] using congrArg (fun f : ℤ →+ ℤ => f n) hχHom

end Omega.Conclusion
