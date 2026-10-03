import Chapter4VectorPicardIterates
import Chapter4VectorPicardL2
import Chapter4PrefixIntegralBound

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Finite-horizon vector SDE existence, assembled from the actual Ito
integral construction, Volterra iteration, factorial summability and L²
continuity. Only the manuscript coefficient and initial-data hypotheses
are supplied; no iteration or fixed-point estimate is assumed. -/
theorem vector_sde_finite_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    : ∃ (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
        (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ),
      Measurable[m] Y ∧ MemLp Y 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r)) ∧
      (∀ i j,LocalMProcessWitness P F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j)
        (fun z => σ i j (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N i j)) ∧
      ∀ᵐ w ∂P,∀ r i,Y w r i=ξ w i+(∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)))+∑ j,N i j (realTimeClamp r.val) w := by
  letI : MeasurableSpace Ω := m
  obtain ⟨X,Z,hX0,hm,hi,ha,hZ,hZI,hrep⟩ := finite_picard_iterates P hT F hF hle hnull
    W C hW hC hclock R hR hRT L hL μ σ hμ hσ hμLip hσLip ξ hξ hξi
  let c := (dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L
  have hc : 0≤c := by dsimp [c]; positivity
  have hstep n t (ht : t∈Icc 0 R) :
      (∫ w,‖prefixPath hR (X (n+2) w-X (n+1) w) t‖^2 ∂P)≤
        c*(∫ r in 0..t,(∫ w,‖prefixPath hR (X (n+1) w-X n w) r‖^2 ∂P)) :=
    finite_picard_prefix_difference P hT F hF hle hnull W C hW hC hclock
      R hR hRT L hL μ σ hμ hσ hμLip hσLip ξ (X (n+1)) (X n) (X (n+2)) (X (n+1))
      (hm (n+1)) (hm n) (hi (n+1)) (hi n) (ha (n+1)) (ha n) (hm (n+2)) (hm (n+1))
      (Z (n+1)) (Z n) (hZ (n+1)) (hZ n) (hZI (n+1)) (hZI n) (.of_forall (hrep (n+1))) (.of_forall (hrep n)) t ht
  obtain ⟨Y,hYm,hYa,hYi,hYlim,hYL2⟩ := volterra_adapted_path_limit P R hR
    (fun r => F (realTimeClamp r.val)) (fun r => hnull (realTimeClamp r.val)) X hm hi ha c hc hstep
  obtain ⟨V,N,hVm,hVi,hVa,hN,hNI,hVrep⟩ := finite_picard_image P hT F hF hle hnull
    W C hW hC hclock R hR hRT L hL μ σ hμ hσ hμLip hσLip ξ hξ hξi Y hYm hYi hYa
  have hbound n : eLpNorm (fun w => X (n+1) w-V w) 2 P≤
      ENNReal.ofReal (Real.sqrt (c*R))*eLpNorm (fun w => Y w-X n w) 2 P := by
    have h := finite_picard_L2_difference P hT F hF hle hnull W C hW hC hclock
      R hR hRT L hL μ σ hμ hσ hμLip hσLip ξ (X n) Y (X (n+1)) V (hm n) hYm (hi n) hYi
      (ha n) hYa (hm (n+1)) hVm (Z n) N (hZ n) hN (hZI n) hNI (.of_forall (hrep n)) (.of_forall hVrep) (hi (n+1)) hVi
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
  filter_upwards [hYV] with w hw
  intro r i
  exact (congrArg (fun p : C(Icc (0:ℝ) R,Fin dim → ℝ) => p r i) hw).trans (hVrep w r i)

end Asakura.Chapter4.Vector
