import Chapter13HJMParameterExponent

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- An a.e. drift identity on the open time interval determines every
primitive up to its endpoint, including the displayed maturity-time formula. -/
theorem hjm_drift_primitive_substitution (b q:ℝ → ℝ) (R:ℝ)
    (he:∀ᵐr∂volume,r∈Ioo 0 R → b r=-q r/2) :
    ∀t∈Icc 0 R,(∫r in 0..t,b r)=-(∫r in 0..t,q r)/2 := by
  intro t ht
  have hEq:(fun r => b r)=ᵐ[volume.restrict (Ioo 0 t)] (fun r => -q r/2) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [he] with r hr hri
    exact hr ⟨hri.1,hri.2.trans_le ht.2⟩
  have hEq':(fun r => b r)=ᵐ[volume.restrict (Ioc 0 t)] (fun r => -q r/2) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hEq
  rw [intervalIntegral.integral_of_le ht.1]
  rw [integral_congr_ae hEq',integral_div,integral_neg,←intervalIntegral.integral_of_le ht.1]

/-- Substitution into the actual exponent yields the HJM stochastic
exponential representation, without making the drift identity pointwise. -/
theorem hjm_exponent_after_drift (b q:ℝ → ℝ) (R ξ:ℝ) (X N:ℝ → ℝ)
    (he:∀ᵐr∂volume,r∈Ioo 0 R → b r=-q r/2)
    (hX:∀t∈Icc 0 R,X t=ξ+(∫r in 0..t,b r)+N t) :
    ∀t∈Icc 0 R,Real.exp (X t)=Real.exp ξ*Real.exp (-(∫r in 0..t,q r)/2+N t) := by
  intro t ht
  rw [hX t ht,hjm_drift_primitive_substitution b q R he t ht,←Real.exp_add]
  congr 1
  ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_drift_primitive_substitution
#print axioms Asakura.Chapter13.hjm_exponent_after_drift
