import Chapter5FiniteTimeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The final integration in the Y estimate, with the actual weighted
sample-time integral and the Fubini hypotheses derived from L². -/
theorem integrated_pointwise_energy_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (β : ℝ) (hβ : 0 ≤ β)
    (Y : Ω × ℝ → ℝ) (hY : Measurable Y)
    (hi : MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))))
    (K : ℝ) (hb : ∀ t ∈ Ioc 0 R, (∫ w,Real.exp (β*t)*Y (w,t)^2 ∂P) ≤ K) :
    (∫ w, (∫ r in 0..R,Real.exp (β*r)*Y (w,r)^2) ∂P) ≤ R*K := by
  obtain ⟨hw,_,_,hswap⟩ := finite_time_weighted_energy P R hR β hβ Y hY hi
  rw [hswap,intervalIntegral.integral_of_le hR]
  have hbound : ∀ᵐ r ∂volume.restrict (Ioc 0 R),
      (∫ w,Real.exp (β*r)*Y (w,r)^2 ∂P) ≤ K :=
    (ae_restrict_mem measurableSet_Ioc).mono fun r hr => hb r hr
  have hh := integral_mono_ae hw.integral_prod_right (integrable_const K) hbound
  have he : (∫ _ : ℝ in Ioc 0 R, K) = R*K := by
    rw [integral_const,smul_eq_mul]
    simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hR]
  exact hh.trans_eq he

end Asakura.Chapter5
