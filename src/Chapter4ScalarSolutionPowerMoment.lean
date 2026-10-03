import Chapter4ScalarUniformPowerBound
import Chapter4StoppedFiniteEquation
import Chapter4StoppedBrownianIntegral
import Chapter4PowerMomentLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Finite p-moments of an arbitrary actual scalar SDE solution. No moment
assumption is made on the solution path. The proof constructs level stops,
uses the actual drift and Ito integral estimate, and removes the stops. -/
theorem scalar_solution_power_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (G : Ω × ℝ → ℝ)
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n))
    (hNI : ItoCovarianceFormula P F W G N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (p : ℝ) (hp : 2≤p)
    (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (hYm : Measurable[m] Y) (ha : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r))
    (hi0 : MemLp (fun w => Y w (finitePrefixTime (T := T) R hR ⊥)) (ENNReal.ofReal p) P)
    (ξ : Ω → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ (ENNReal.ofReal p) P)
    (U : Ω × ℝ → ℝ) (hUm : Measurable[m.prod inferInstance] U) (hGm : Measurable[m.prod inferInstance] G)
    (K : ℝ) (hK : 0≤K)
    (hUg : ∀ w r,r∈Icc 0 R → |U (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (hGg : ∀ w r,r∈Icc 0 R → |G (w,r)|^p≤K*(1+|Y w (projIcc 0 R hR r)|^p))
    (hrep : ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,U (w,s))+N (realTimeClamp r.val) w) :
    MemLp Y (ENNReal.ofReal p) P := by
  classical
  letI : MeasurableSpace Ω := m
  have hp0 : 0<p := by linarith only [hp]
  obtain ⟨τ,Z,hτ,hτmono,hτtop,hτR,hZm,hZi,hZa,he,hlim⟩ :=
    finite_path_moment_stops P F hF hle R hR hRT Y ha (ENNReal.ofReal p) hi0
  let B := ((3:ℝ)^(p-1)*(∫ w,|ξ w|^p ∂P)+momentGrowthRate R p K*R)*
    Real.exp ((momentGrowthRate R p K+1)*R)
  have hbound n : (∫ w,‖Z n w‖^p ∂P)≤B := by
    let V := fun z : Ω × ℝ => (Ioc (⊥ : ClosedTime T) (τ n z.1)).indicator (fun _ => U z) (realTimeClamp z.2)
    let H := fun z : Ω × ℝ => (Ioc (⊥ : ClosedTime T) (τ n z.1)).indicator (fun _ => G z) (realTimeClamp z.2)
    obtain ⟨J,hJ,hJI,hJe,hHp,hHi⟩ := stopped_brownian_integral_constructed P hT F hF hle hnull
      W A N hW hA hN c hc hcm hcT hct hcut hcc hclock G hG hi hNI (τ n) (hτtop n) (hτ n)
    have htm := bounded_stopping_time_measurable F hF hle (τ n) (hτ n) (realTimeClamp R) (hτR n)
    exact scalar_integral_uniform_power_bound P hT F hF hle hnull W A J hW hA hJ
      c hc hcm hcT hct hcut hcc hclock H hHp hHi hJI R hR hRT p hp (Z n) (hZm n) (hZi n)
      ξ hξm hξi V (stopped_integrand_joint_measurable (τ n) htm U hUm)
      (stopped_integrand_joint_measurable (τ n) htm G hGm) K hK
      (stopped_finite_coefficient_growth R hR hRT Y (Z n) (τ n) (he n) U p K hp0 hK hUg)
      (stopped_finite_coefficient_growth R hR hRT Y (Z n) (τ n) (he n) G p K hp0 hK hGg)
      (stopped_finite_equation P R hR hRT Y (Z n) (τ n) (hτtop n) (hτR n) (he n) ξ U N J hrep hJe)
  have hB : 0≤B := (integral_nonneg (fun w => Real.rpow_nonneg (norm_nonneg _) _)).trans (hbound 0)
  apply power_moment_limit P Y hYm.aestronglyMeasurable Z p hp0 hZi B hB hbound
  apply Filter.Eventually.of_forall
  intro w
  exact tendsto_const_nhds.congr' ((hlim w).mono (fun _ h => h.symm))

end Asakura.Chapter4
