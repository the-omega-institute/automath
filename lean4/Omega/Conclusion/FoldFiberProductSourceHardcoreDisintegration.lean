import Omega.POM.FiberBiasedBernoulliPushforwardHardcore

namespace Omega.Conclusion

theorem paper_conclusion_fold_fiber_product_source_hardcore_disintegration
    (D : Omega.POM.FiberBiasedBernoulliPushforwardHardcoreData) :
    D.pushforwardClosedForm ∧ D.posteriorHardcoreForm ∧
      D.posteriorMatchesIndependentSetModel := by
  simpa using Omega.POM.paper_pom_fiber_biased_bernoulli_pushforward_hardcore D

end Omega.Conclusion
