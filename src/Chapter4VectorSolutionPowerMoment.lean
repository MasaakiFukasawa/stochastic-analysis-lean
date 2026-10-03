import Chapter4VectorUniformPowerBound
import Chapter4VectorMomentStops
import Chapter4ScalarSolutionPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem vector_solution_power_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    {d dim : ℕ} (W A : Fin d → ClosedTime T → Ω → ℝ) (N : Fin dim → Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ j n w r, r ∈ Icc 0 (c n) → A j (realTimeClamp r) w = r)
    (G : Fin dim → Fin d → Ω × ℝ → ℝ)
    (hG : ∀ i j n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G i j (z.1,z.2.val)))
    (hi : ∀ i j n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G i j (w,r)^2) volume 0 (c n))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (G i j) (N i j))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hYm : Measurable[m] Y) 
    (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (hi0 : MemLp (fun w => Y w (finitePrefixTime (T := T) R hR ⊥)) (ENNReal.ofReal p) P)
    (ξ : Fin dim → Ω → ℝ) (hξm : ∀ i,Measurable[m] (ξ i)) (hξi : ∀ i,MemLp (ξ i) (ENNReal.ofReal p) P)
    (U : Fin dim → Ω × ℝ → ℝ) (hUm : ∀ i,Measurable[m.prod inferInstance] (U i)) (hGm : ∀ i j,Measurable[m.prod inferInstance] (G i j))
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ i w r,r∈Icc 0 R → |U i (w,r)|^p≤K*(1+‖Y w (projIcc 0 R hR r)‖^p))
    (hGg : ∀ i j w r,r∈Icc 0 R → |G i j (w,r)|^p≤K*(1+‖Y w (projIcc 0 R hR r)‖^p))
    (hrep : ∀ᵐ w ∂P,∀ r i,Y w r i=ξ i w+(∫ s in 0..r.val,U i (w,s))+∑ j,N i j (realTimeClamp r.val) w) :
    MemLp Y (ENNReal.ofReal p) P := by
  classical
  letI : MeasurableSpace Ω := m
  have hp0 : 0<p := by linarith only [hp]
  obtain ⟨τ,Z,hτ,hτmono,hτtop,hτR,hZm,hZi,hZa,he,hlim⟩ :=
    Vector.finite_path_moment_stops P F hF hle R hR hRT Y ha (ENNReal.ofReal p) hi0
  let α := (dim:ℝ)^(p-1)*(3:ℝ)^(p-1)
  let δ := (d:ℝ)^(p-1)*d
  let rate := vectorMomentGrowthRate R p K α dim δ
  let B := (α*(∑ i,∫ w,|ξ i w|^p ∂P)+rate*R)*Real.exp ((rate+1)*R)
  have hbound n : (∫ w,‖Z n w‖^p ∂P)≤B := by
    let V := fun i (z : Ω × ℝ) => (Ioc (⊥ : ClosedTime T) (τ n z.1)).indicator (fun _ => U i z) (realTimeClamp z.2)
    let H := fun i j (z : Ω × ℝ) => (Ioc (⊥ : ClosedTime T) (τ n z.1)).indicator (fun _ => G i j z) (realTimeClamp z.2)
    have hj i j := stopped_brownian_integral_constructed P hT F hF hle hnull
      (W j) (A j) (N i j) (hW j) (hA j) (hN i j) c hc hcm hcT hct hcut hcc (hclock j)
      (G i j) (hG i j) (hi i j) (hNI i j) (τ n) (hτtop n) (hτ n)
    let J := fun i j => (hj i j).choose
    have htm := bounded_stopping_time_measurable F hF hle (τ n) (hτ n) (realTimeClamp R) (hτR n)
    have hnorm w r : normEnvelope (Z n w) r=normEnvelope (Y w) (finitePrefixTime (T := T) R hR (min (τ n w) (realTimeClamp r.val))) :=
      congrArg norm (he n w r)
    have hVg i := stopped_finite_coefficient_growth R hR hRT
      (fun w => normEnvelope (Y w)) (fun w => normEnvelope (Z n w)) (τ n) hnorm (U i) p K hp0 hK
      (by simpa only [normEnvelope,ContinuousMap.coe_mk,abs_norm] using hUg i)
    have hHg i j := stopped_finite_coefficient_growth R hR hRT
      (fun w => normEnvelope (Y w)) (fun w => normEnvelope (Z n w)) (τ n) hnorm (G i j) p K hp0 hK
      (by simpa only [normEnvelope,ContinuousMap.coe_mk,abs_norm] using hGg i j)
    have hJsum i : ∀ᵐ w ∂P,∀ t,t<⊤ → (∑ j,J i j t w)=∑ j,N i j (min (τ n w) t) w := by
      have hh : ∀ᵐ w ∂P,∀ j,∀ t,t<⊤ → J i j t w=N i j (min (τ n w) t) w :=
        ae_all_iff.mpr (fun j => (hj i j).choose_spec.2.2.1)
      filter_upwards [hh] with w hw
      intro t ht
      exact Finset.sum_congr rfl (fun j _ => hw j t ht)
    have hrep' i := stopped_finite_equation P R hR hRT
      (fun w => coordinateRealPath (Y w) i) (fun w => coordinateRealPath (Z n w) i)
      (τ n) (hτtop n) (hτR n) (fun w r => congrFun (he n w r) i)
      (ξ i) (U i) (fun t w => ∑ j,N i j t w) (fun t w => ∑ j,J i j t w)
      (hrep.mono (fun w hw r => hw r i)) (hJsum i)
    have hrepZ : ∀ᵐ w ∂P,∀ r i,Z n w r i=ξ i w+(∫ s in 0..r.val,V i (w,s))+∑ j,J i j (realTimeClamp r.val) w := by
      filter_upwards [ae_all_iff.mpr hrep'] with w hw
      exact fun r i => hw i r
    exact vector_integral_uniform_power_bound P hT F hF hle hnull W A J hW hA
      (fun i j => (hj i j).choose_spec.1) c hc hcm hcT hct hcut hcc hclock H
      (fun i j => (hj i j).choose_spec.2.2.2.1) (fun i j => (hj i j).choose_spec.2.2.2.2)
      (fun i j => (hj i j).choose_spec.2.1) R hR hRT p hp (Z n) (hZm n) (hZi n)
      ξ hξm hξi V (fun i => stopped_integrand_joint_measurable (τ n) htm (U i) (hUm i))
      (fun i j => stopped_integrand_joint_measurable (τ n) htm (G i j) (hGm i j)) K hK
      (by simpa only [normEnvelope,ContinuousMap.coe_mk,abs_norm] using hVg)
      (by simpa only [normEnvelope,ContinuousMap.coe_mk,abs_norm] using hHg) hrepZ
  have hB : 0≤B := (integral_nonneg (fun w => Real.rpow_nonneg (norm_nonneg _) _)).trans (hbound 0)
  apply power_moment_limit P Y hYm.aestronglyMeasurable Z p hp0 hZi B hB hbound
  apply Filter.Eventually.of_forall
  intro w
  exact tendsto_const_nhds.congr' ((hlim w).mono (fun _ h => h.symm))

end Asakura.Chapter4
