import Chapter11ExponentialSDE
import Chapter11ExponentialMoments
import Chapter11WeightedEnergy

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- In the constructed exponential SDE, the stochastic term is a genuine
M2 martingale on the finite horizon. All real wealth moments are available. -/
theorem exponential_sde_integrable_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)))
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K L x R : ℝ) (hK : 0≤K) (hL : 0≤L)
    (hHb : ∀ z,|H z|≤K) (hbb : ∀ z,|b z|≤L) (hR : 0<R) :
    ∃ V N M : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ LocalMProcessWitness P B.F M ∧
      ItoCovarianceFormula P B.F (B.W 0) H N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*H z) M ∧
      (∀ w t,0<V t w) ∧
      (∀ w t,t∈Icc 0 R → V (realTimeClamp t) w=Real.exp (x+(∫ s in 0..t,b (w,s))+N (realTimeClamp t) w)) ∧
      (∀ t∈Icc 0 R,V (realTimeClamp t)=ᵐ[P]
        fun w => Real.exp x+(∫ s in 0..t,V (realTimeClamp s) w*(b (w,s)+(H (w,s))^2/2))+M (realTimeClamp t) w) ∧
      Measurable (fun z : Ω × ℝ => V (realTimeClamp z.2) z.1) ∧
      (∀ q : ℝ,Integrable (fun z : Ω × ℝ => (V (realTimeClamp z.2) z.1)^q)
        (P.prod (volume.restrict (Icc 0 R)))) ∧
      (∀ q : ℝ,Integrable (fun w => (V (realTimeClamp R) w)^q) P) ∧
      ContinuousM2Witness P B.F (fun t w => M (min (realTimeClamp R) t) w) ∧
      Integrable (M (realTimeClamp R)) P ∧ (∫ w,M (realTimeClamp R) w ∂P)=0 := by
  obtain ⟨V,N,M,hN,hM,hNI,hMI,hpos,he,hsde,hVa,hVc⟩ := exponential_bounded_sde_constructed
    P B b H hbm hHm hbp hHp K L x R hK hHb hbb hR
  obtain ⟨hVm,hVp,hVi⟩ := continuous_weight_bounded_energy P B H hHm hHp K hK hHb V hVa hVc
  have hmo q t (ht : t∈Icc 0 R) :
      Integrable (fun w => (V (realTimeClamp t) w)^q) P ∧
      (∫ w,(V (realTimeClamp t) w)^q ∂P)≤(Real.exp x)^q*Real.exp (|q| *(L*R+K^2*R/2)+|q^2-q| *(K^2*R)/2) := by
    simpa only [he _ _ ht] using bounded_exponential_real_moments P B b H hbm hHm hHp K L x R
      hK hL hHb hbb N hN hNI q t ht
  have htime (q : ℝ) : Integrable (fun z : Ω × ℝ => (V (realTimeClamp z.2) z.1)^q)
      (P.prod (volume.restrict (Icc 0 R))) :=
    uniform_moments_time_integrable P _ hVm (fun z => hpos _ _) q R
      ((Real.exp x)^q*Real.exp (|q| *(L*R+K^2*R/2)+|q^2-q| *(K^2*R)/2))
      (fun t ht => (hmo q t ht).1) (fun t ht => (hmo q t ht).2)
  have hv2 : MemLp (fun z : Ω × ℝ => V (realTimeClamp z.2) z.1) 2 (P.prod (volume.restrict (Icc 0 R))) := by
    apply (memLp_two_iff_integrable_sq hVm.aestronglyMeasurable).mpr
    simpa using htime (2:ℝ)
  have hhinfty : MemLp H ∞ (P.prod (volume.restrict (Icc 0 R))) :=
    MemLp.of_bound hHm.aestronglyMeasurable K (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hHb z))
  have hG2 : Integrable (fun z : Ω × ℝ => (V (realTimeClamp z.2) z.1*H z)^2)
      (P.prod (volume.restrict (Icc 0 R))) :=
    (memLp_two_iff_integrable_sq (hVm.mul hHm).aestronglyMeasurable).mp (hv2.mul hhinfty)
  have hm := brownian_finite_energy_mean_zero P B _ (hVm.mul hHm) hVp hVi M hM hMI R hR.le hG2
  exact ⟨V,N,M,hN,hM,hNI,hMI,hpos,he,hsde,hVm,htime,fun q => (hmo q R ⟨hR.le,le_rfl⟩).1,hm⟩

end Asakura.Chapter11
