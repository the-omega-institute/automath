import Mathlib.Algebra.Group.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-localized-dual-finite-group-certificate-constant`. Once the
finite-group quotient map is constant, any certificate read through it is constant as well. -/
theorem paper_conclusion_localized_dual_finite_group_certificate_constant
    {Sigma H F : Type*} [Group H] (pi : Sigma → H) (beta : H → F)
    (hpi : Exists fun e : H => ∀ x : Sigma, pi x = e) :
    Exists fun c : F => ∀ x : Sigma, beta (pi x) = c := by
  rcases hpi with ⟨e, he⟩
  exact ⟨beta e, fun x => by rw [he x]⟩

end Omega.Conclusion
