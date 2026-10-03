import Chapter4FlowSDEConstructed
import Chapter4FlowCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

lemma flow_composition_derivative
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hflow : ∀ x y,fderiv ℝ φ ![x,y] (Pi.single 0 1)=f (φ ![x,y])) (x y : ℝ) :
    fderiv ℝ (fun z => f (φ z)) ![x,y] (Pi.single 0 1)=deriv f (φ ![x,y])*f (φ ![x,y]) := by
  have hx := ((hφ.differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt x
    (fin2_time_slice_derivative x y)
  rw [hflow x y] at hx
  have hr := (((hf.comp hφ).differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt x
    (fin2_time_slice_derivative x y)
  exact hr.unique (((hf.differentiable (by norm_num)) _).hasDerivAt.comp x hx)

/-- Both forms of the random-ODE construction, including the actual
covariation in the definition of the Stratonovich integral. -/
theorem flow_random_ode_stratonovich
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W Y A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (hYa : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hflow : ∀ x y,fderiv ℝ φ ![x,y] (Pi.single 0 1)=f (φ ![x,y]))
    (hinit : ∀ y,φ ![0,y]=y)
    (hd : ∀ w (r : ℝ),0<r → (r:EReal)<T →
      HasDerivAt (fun s => Y (realTimeClamp s) w)
        (g (φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w])/
          fderiv ℝ φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w] (Pi.single 1 1)) r) :
    let X := fun t w => φ ![W t w,Y t w]
    ∃ N B L C : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => f (X (realTimeClamp z.2) z.1)) N ∧
      SemimartingaleDecomposition P F (fun t w => f (X t w)) B L ∧
      LocalCovarianceWitness P F L W C ∧
      ∀ (d : ℝ),0≤d → (d:EReal)<T →
        X (realTimeClamp d)=ᵐ[P] fun w => X ⊥ w+
          (N (realTimeClamp d) w+C (realTimeClamp d) w/2)+∫ r in 0..d,g (X (realTimeClamp r) w) := by
  dsimp only
  obtain ⟨hY,N,hN,hNI,hIto⟩ := flow_random_ode_constructed_sde P hT F hF hle hnull
    W Y A hW hA hclock hYa hYc φ hφ f g (hf.of_le (by norm_num)) hg hflow hinit hd
  obtain ⟨c,hc0,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  let hc := fun n => (hc0 n).le
  obtain ⟨B,L,C,J,hL,hC,hJ,heC⟩ := martingale_variation_composition_covariance P hT F hF hle hnull
    W Y A hW hY hYc hA (fun z => f (φ z)) (hf.comp hφ) c hc hcm.monotone hcT hcc
  refine ⟨N,B,L,C,hN,hNI,hL,hC,?_⟩
  intro d hd0 hdT
  have hdt := real_time_below d hd0 hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d≤c j := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq d hd0 hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact (EReal.coe_lt_coe_iff.mp hj).le
  have hJi := clock_variation_integral_at_time P A J _ c hc hcT
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) hJ j d hd0 hdj
  filter_upwards [hIto d hd0 hdT,heC,hJi] with w hi hcw hjw
  have hcid : C (realTimeClamp d) w=∫ r in 0..d,
      deriv f (φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w])*
        f (φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w]) := by
    rw [hcw _ hdt,hjw]
    apply intervalIntegral.integral_congr
    intro r _
    exact flow_composition_derivative φ hφ f hf hflow _ _
  have hvc : ContinuousOn (fun r : ℝ => φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w]) (Icc 0 d) := by
    apply hφ.continuous.comp_continuousOn
    intro r hr
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact (hW.path P F w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hdT))).comp
        real_time_clamp_continuous.continuousAt
    · exact (hYc w _ (real_time_below r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hdT))).comp
        real_time_clamp_continuous.continuousAt
  have h1 := (hg.comp_continuousOn hvc).intervalIntegrable_of_Icc (μ := volume) hd0
  have h2 := (((hf.continuous_deriv (by norm_num)).comp_continuousOn hvc).mul
    (hf.continuous.comp_continuousOn hvc)).intervalIntegrable_of_Icc (μ := volume) hd0
  dsimp only [Function.comp_def,Pi.mul_apply] at h1 h2
  change IntervalIntegrable (fun r => deriv f (φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w])*f (φ ![W (realTimeClamp r) w,Y (realTimeClamp r) w])) volume 0 d at h2
  rw [intervalIntegral.integral_add h1 (h2.div_const 2),intervalIntegral.integral_div] at hi
  rw [hcid]
  linarith

end Asakura.Chapter4
