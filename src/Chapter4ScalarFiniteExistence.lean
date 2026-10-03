import Chapter4FinitePicardIterates
import Chapter4FinitePicardL2
import Chapter4ClockRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon scalar SDE existence, assembled from the actual Ito
integral construction, Volterra iteration, factorial summability and L²
continuity. Only the manuscript coefficient and initial-data hypotheses
are supplied; no iteration or fixed-point estimate is assumed. -/
theorem scalar_sde_finite_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L) (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y,(μ x-μ y)^2+(σ x-σ y)^2≤L*(x-y)^2)
    (ξ : Ω → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    : ∃ (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (N : ClosedTime T → Ω → ℝ),
      Measurable[m] Y ∧ MemLp Y 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r)) ∧
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => σ (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N ∧
      ∀ᵐ w ∂P,∀ r,Y w r=ξ w+(∫ s in 0..r.val,μ (Y w (projIcc 0 R hR s)))+N (realTimeClamp r.val) w := by
  letI : MeasurableSpace Ω := m
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  obtain ⟨X,Z,hX0,hm,hi,ha,hZ,hZI,hrep⟩ := finite_picard_iterates P hT F hF hle hnull
    W C hW hC hCm hCc hclock R hR hRT L hL μ σ hμ hσ hLip ξ hξ hξi
  let c := (2*R+8)*L
  have hc : 0≤c := by dsimp [c]; positivity
  have hstep n t (ht : t∈Icc 0 R) :
      (∫ w,‖prefixPath hR (X (n+2) w-X (n+1) w) t‖^2 ∂P)≤
        c*(∫ r in 0..t,(∫ w,‖prefixPath hR (X (n+1) w-X n w) r‖^2 ∂P)) :=
    finite_picard_prefix_difference P hT F hF hle hnull W C hW hC hCm hCc hclock
      R hR hRT L hL μ σ hμ hσ hLip ξ (X (n+1)) (X n) (X (n+2)) (X (n+1))
      (hm (n+1)) (hm n) (hi (n+1)) (hi n) (ha (n+1)) (ha n) (hm (n+2)) (hm (n+1))
      (Z (n+1)) (Z n) (hZ (n+1)) (hZ n) (hZI (n+1)) (hZI n) (hrep (n+1)) (hrep n) t ht
  obtain ⟨Y,hYm,hYa,hYi,hYlim,hYL2⟩ := volterra_adapted_path_limit P R hR
    (fun r => F (realTimeClamp r.val)) (fun r => hnull (realTimeClamp r.val)) X hm hi ha c hc hstep
  obtain ⟨V,N,hVm,hVi,hVa,hN,hNI,hVrep⟩ := finite_picard_image P hT F hF hle hnull
    W C hW hC hCm hCc hclock R hR hRT L hL μ σ hμ hσ hLip ξ hξ hξi Y hYm hYi hYa
  have hbound n : eLpNorm (fun w => X (n+1) w-V w) 2 P≤
      ENNReal.ofReal (Real.sqrt (c*R))*eLpNorm (fun w => Y w-X n w) 2 P := by
    have h := finite_picard_L2_difference P hT F hF hle hnull W C hW hC hCm hCc hclock
      R hR hRT L hL μ σ hμ hσ hLip ξ (X n) Y (X (n+1)) V (hm n) hYm (hi n) hYi
      (ha n) hYa (hm (n+1)) hVm (Z n) N (hZ n) hN (hZI n) hNI (hrep n) hVrep (hi (n+1)) hVi
    have hnorm := eLpNorm_sub_comm (X n) Y (2:ℝ≥0∞) P
    simp only [Pi.sub_def] at hnorm
    simpa only [hnorm] using h
  have hlimV : Tendsto (fun n => eLpNorm (fun w => X (n+1) w-V w) 2 P) atTop (𝓝 0) := by
    have hh := (ENNReal.continuous_const_mul (by simp : ENNReal.ofReal (Real.sqrt (c*R))≠∞)).tendsto 0 |>.comp hYL2
    have hh' : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (c*R))*eLpNorm (fun w => Y w-X n w) 2 P) atTop (𝓝 0) := by
      simpa only [Function.comp_def,mul_zero] using hh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0:ℝ≥0∞))) hh' (fun _ => bot_le) hbound
  have hYV := ae_eq_of_two_L2_limits P (fun n => X (n+1)) Y V
    (hYL2.comp (tendsto_add_atTop_nat 1)) hlimV
  refine ⟨Y,N,hYm,hYi,hYa,hN,hNI,?_⟩
  filter_upwards [hYV,hVrep] with w hw hv
  intro r
  exact (congrArg (fun p : C(Icc (0:ℝ) R,ℝ) => p r) hw).trans (hv r)

end Asakura.Chapter4
