---
name: Formalization pipeline state
description: Current round count, annotation counts, coverage, and recent round history for the Lean4 formalization pipeline
type: project
---

Pipeline state as of 2026-04-05 (orchestrator refresh 2, shutdown):

- round_count = 255 (R254 fully registered, R255 dispatched to formalizer-2 but not yet completed)
- \leanverified = ~926, \leanpartial = 17, total annotations = ~943
- body coverage = ~877/10,508 = ~8.3%
- theorems ~3,500+

R255 status: spec dispatched to formalizer-2 (SPG kappa algebraic + GU fIC exponential + Conclusion Fibonacci growth), awaiting completion. No commit yet.

Recent rounds:
- R250: A4(t) parametric kernel (POM) + binary auxbits (Conclusion) + Hankel-4 (Zeta)
- R251: Chebyshev-Adams semigroup law (Discussion) + kappa inverse (SPG) + circleDim scaling (CD)
- R252 partial: BF5 det (POM) + Fibonacci growth (Conclusion), Fredholm symbolic det deferred
- R253: chebyAdams extensions (Discussion) + free involution exists (GU) + BF5 consistency (Folding)
- R254: multiPrimeSpectrum (CD) + cyclicPerm trace (Zeta) + collisionKernel5_e2 (POM)
- R255 in progress: kappa algebra (SPG) + fIC exponential bound (GU) + fib growth (Conclusion)

Chapter coverage: POM ~13.4%, EA 51.9%, Folding 24.0%, Conclusion ~6.0%, GU ~18.2%, SPG ~29.5%, CD ~18.9%, Zeta ~2.5%, Discussion ~15%

Deferred items:
- weight_eq_fib_sub_one_unique (R249 T1, Folding direction)
- collisionKernel4_fredholm_det symbolic z (R252 T1, 5x5 symbolic det expansion timeout)

**Why:** Track progress for orchestrator refresh continuity.
**How to apply:** Use these numbers as baseline for next orchestrator spawn. R255 may already be completed by formalizer-2 -- check git log on startup.
