import Chapter7BrownianGridIntegrand

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The estimator's grid martingale and its actual quadratic variation,
constructed from the given Brownian driver. -/
theorem brownian_grid_martingale_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (h a : ℝ) (hh : 0≤h) (n : ℕ) :
    ∃ (N : Fin d → HalfClosedTime → Ω → ℝ) (C : HalfClosedTime → Ω → ℝ),
      (∀ i,LocalMProcessWitness P B.F (N i)) ∧
      (∀ i,ItoCovarianceFormula P B.F (B.W i)
        (fun z => a*brownianGridIntegrand B (K i) h n z) (N i)) ∧
      LocalMProcessWitness P B.F (fun t w => ∑ i,N i t w) ∧
      LocalCovarianceWitness P B.F (fun t w => ∑ i,N i t w) (fun t w => ∑ i,N i t w) C ∧
      (∀ b : ℝ,0≤b → C (realTimeClamp b) =ᵐ[P] fun w =>
        ∫ r in 0..b,∑ i,(a*brownianGridIntegrand B (K i) h n (w,r))^2) := by
  let H := fun i z => a*brownianGridIntegrand B (K i) h n z
  have hr i := brownian_grid_integrand_regular P B (K i) h hh n
  have hm i : Measurable (H i) := measurable_const.mul (hr i).1
  have hp i b (hb : 0<b) : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H i (z.1,z.2.val)) :=
    measurable_const.mul ((hr i).2.1 b hb.le)
  have hsq i b (hb : 0≤b) w : IntervalIntegrable (fun r => (H i (w,r))^2) volume 0 b := by
    simpa only [H,mul_pow] using ((hr i).2.2 b hb w).const_mul (a^2)
  obtain ⟨N,hN,hNI⟩ := locally_square_integrable_vector_integrals P B H hm hp
    (fun i b hb => ae_of_all _ (fun w => hsq i b hb.le w))
  have hlp i w b (hb : 0≤b) : MemLp (fun r => H i (w,r)) 2 (volume.restrict (Ioc 0 b)) := by
    apply (memLp_two_iff_integrable_sq ((hm i).comp measurable_prodMk_left).aestronglyMeasurable).mpr
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp (hsq i b hb w)
  have hi i w b (hb : 0≤b) : IntervalIntegrable (fun r => H i (w,r)) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr ((hlp i w b hb).integrable (by norm_num))
  have hpi i j w b (hb : 0≤b) : IntervalIntegrable (fun r => H i (w,r)*H j (w,r)) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr ((hlp i w b hb).integrable_mul (hlp j w b hb))
  obtain ⟨hZ,C,L,hC,hL,hCe,hLe⟩ := locally_integrable_vector_covariances P B H hm hi hpi N hN hNI
  exact ⟨N,C,hN,hNI,hZ,hC,hCe⟩

end Asakura.Chapter7
