import Chapter5FiniteTimeEnergy
import Chapter5IntegratedYoung

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Complete the expectation and absorption part at a fixed time. The
energy identity and zero-mean noise are supplied by
bsde_constructed_energy_and_zero_mean, not by formal differential notation. -/
theorem apriori_at_time_from_constructed_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (β C l m : ℝ)
    (hC : 0 ≤ C) (hl : C < l) (hm : 0 < m) (hβ : C*(2+l)+m ≤ β)
    (Y Z D F : Ω × ℝ → ℝ)
    (hYm : Measurable Y) (hZm : Measurable Z) (hDm : Measurable D) (hFm : Measurable F)
    (hY : MemLp Y 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hZ : MemLp Z 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hD : MemLp D 2 (P.prod (volume.restrict (Ioc 0 R))))
    (hξ : MemLp (fun w => Y (w,R)) 2 P)
    (hbound : ∀ w r, r ∈ Icc 0 R → |F (w,r)| ≤ C*(|Y (w,r)|+|Z (w,r)|)+|D (w,r)|)
    (t : ℝ) (ht : t ∈ Icc 0 R) (hYt : MemLp (fun w => Y (w,t)) 2 P)
    (N : Ω → ℝ) (hNi : Integrable N P) (hN0 : (∫ w,N w ∂P) = 0)
    (he : ∀ᵐ w ∂P,
      Real.exp (β*t)*Y (w,t)^2 + (∫ r in t..R,β*Real.exp (β*r)*Y (w,r)^2) +
      (∫ r in t..R,Real.exp (β*r)*Z (w,r)^2) =
      Real.exp (β*R)*Y (w,R)^2 + (∫ r in t..R,2*Real.exp (β*r)*Y (w,r)*F (w,r))-N w) :
    (∫ w,Real.exp (β*t)*Y (w,t)^2 ∂P) ≤
      (∫ w,Real.exp (β*R)*Y (w,R)^2 ∂P)+(∫ w,(∫ r in t..R,Real.exp (β*r)*D (w,r)^2) ∂P)/m ∧
    (∫ w,(∫ r in t..R,Real.exp (β*r)*Z (w,r)^2) ∂P) ≤
      l/(l-C)*((∫ w,Real.exp (β*R)*Y (w,R)^2 ∂P)+(∫ w,(∫ r in t..R,Real.exp (β*r)*D (w,r)^2) ∂P)/m) := by
  have hl0 : 0 < l := hC.trans_lt hl
  have hβ0 : 0 ≤ β := (by positivity : 0 ≤ C*(2+l)+m).trans hβ
  obtain ⟨hYpath,hYi⟩ := finite_time_weighted_tail_energy P R hR β hβ0 Y hYm hY t ht
  obtain ⟨hZpath,hZi⟩ := finite_time_weighted_tail_energy P R hR β hβ0 Z hZm hZ t ht
  obtain ⟨hDpath,hDi⟩ := finite_time_weighted_tail_energy P R hR β hβ0 D hDm hD t ht
  have hUt : Integrable (fun w => Real.exp (β*t)*Y (w,t)^2) P :=
    ((memLp_two_iff_integrable_sq hYt.aestronglyMeasurable).mp hYt).const_mul _
  have hUr : Integrable (fun w => Real.exp (β*R)*Y (w,R)^2) P :=
    ((memLp_two_iff_integrable_sq hξ.aestronglyMeasurable).mp hξ).const_mul _
  have hinequality : ∀ᵐ w ∂P,
      Real.exp (β*t)*Y (w,t)^2 + β*(∫ r in t..R,Real.exp (β*r)*Y (w,r)^2) +
      (∫ r in t..R,Real.exp (β*r)*Z (w,r)^2) ≤
      Real.exp (β*R)*Y (w,R)^2 +(2*C+C*l+m)*(∫ r in t..R,Real.exp (β*r)*Y (w,r)^2)+
      (C/l)*(∫ r in t..R,Real.exp (β*r)*Z (w,r)^2)+(∫ r in t..R,Real.exp (β*r)*D (w,r)^2)/m-N w := by
    filter_upwards [he,hYpath,hZpath,hDpath] with w hew hy hz hd
    have hb : ∀ᵐ r ∂volume.restrict (Ioc t R), |F (w,r)| ≤ C*(|Y (w,r)|+|Z (w,r)|)+|D (w,r)| := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hbound w r ⟨ht.1.trans hr.1.le,hr.2⟩
    have hw : AEStronglyMeasurable (fun r : ℝ => Real.exp (β*r)) (volume.restrict (Ioc t R)) :=
      (by fun_prop : Continuous (fun r : ℝ => Real.exp (β*r))).aestronglyMeasurable
    have hh := (integrated_young_generator_bound (volume.restrict (Ioc t R))
      (fun r => Real.exp (β*r)) (fun r => Y (w,r)) (fun r => Z (w,r)) (fun r => D (w,r)) (fun r => F (w,r))
      hw (hYm.comp measurable_prodMk_left).aestronglyMeasurable (hFm.comp measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ fun r => (Real.exp_pos _).le) hy.1 hz.1 hd.1 C l m hC hl0 hm hb).2
    simp only [← intervalIntegral.integral_of_le ht.2] at hh
    have hbeta : (∫ r in t..R,β*Real.exp (β*r)*Y (w,r)^2) = β*(∫ r in t..R,Real.exp (β*r)*Y (w,r)^2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      ring
    rw [hbeta] at hew
    linarith
  exact expected_energy_absorption P
    (fun w => Real.exp (β*t)*Y (w,t)^2) (fun w => ∫ r in t..R,Real.exp (β*r)*Y (w,r)^2)
    (fun w => ∫ r in t..R,Real.exp (β*r)*Z (w,r)^2) (fun w => Real.exp (β*R)*Y (w,R)^2)
    (fun w => ∫ r in t..R,Real.exp (β*r)*D (w,r)^2) N hUt hYi hZi hUr hDi hNi
    (ae_of_all _ fun w => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (ae_of_all _ fun w => intervalIntegral.integral_nonneg ht.2 (fun r _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
    (ae_of_all _ fun w => intervalIntegral.integral_nonneg ht.2 (fun r _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
    hN0 C l m β hC hl hm hβ hinequality

end Asakura.Chapter5
