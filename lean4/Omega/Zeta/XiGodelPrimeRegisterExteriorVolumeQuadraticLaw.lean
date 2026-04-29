namespace Omega.Zeta

/-- Paper label: `thm:xi-godel-prime-register-exterior-volume-quadratic-law`. -/
theorem paper_xi_godel_prime_register_exterior_volume_quadratic_law
    (exactExteriorVolumeLaw primeRegisterSpecialization fixedTAsymptotic quadraticT2Law : Prop)
    (hexact : exactExteriorVolumeLaw)
    (hspecialize : exactExteriorVolumeLaw -> primeRegisterSpecialization)
    (hasymptotic : primeRegisterSpecialization -> fixedTAsymptotic)
    (hquadratic : fixedTAsymptotic -> quadraticT2Law) :
    primeRegisterSpecialization ∧ fixedTAsymptotic ∧ quadraticT2Law := by
  have hprime : primeRegisterSpecialization := hspecialize hexact
  have hfixed : fixedTAsymptotic := hasymptotic hprime
  exact ⟨hprime, hfixed, hquadratic hfixed⟩

end Omega.Zeta
