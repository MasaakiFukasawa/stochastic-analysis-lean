import Chapter4FlowStratonovich
import Chapter4ConstructedODEExample

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The scalar ODE solution composed with Brownian motion solves the
Stratonovich equation; the correction is the actual covariation of f(Y) and W. -/
theorem scalar_ode_stratonovich_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (φ f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hφ : ∀ x,HasDerivAt φ (f (φ x)) x) :
    ∃ N B L C : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => f (φ (W (realTimeClamp z.2) z.1))) N ∧
      SemimartingaleDecomposition P F (fun t w => f (φ (W t w))) B L ∧
      LocalCovarianceWitness P F L W C ∧
      ∀ (d : ℝ),0≤d → (d:EReal)<T →
        (fun w => φ (W (realTimeClamp d) w))=ᵐ[P]
          fun w => φ (W ⊥ w)+N (realTimeClamp d) w+C (realTimeClamp d) w/2 := by
  have hφ2 := ode_solution_c2 φ f (hf.of_le (by norm_num)) hφ
  obtain ⟨c,hc0,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  let hc := fun n => (hc0 n).le
  have hcl n w r (hr : r∈Icc 0 (c n)) := hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  obtain ⟨N,hN,hNI,hIto⟩ := ode_composition_constructed_ito P hT F hF hle hnull W A hW hA
    φ f (hf.of_le (by norm_num)) hφ c hc hcm.monotone hcT hcc hcl
  let ψ := fun z : Fin 2 → ℝ => f (φ (z 0))
  have hψ : ContDiff ℝ 2 ψ := (hf.comp hφ2).comp (contDiff_apply ℝ ℝ (0 : Fin 2))
  have hz : AdaptedLocalVariationWitness F (fun (_ : ClosedTime T) (_ : Ω) => (0:ℝ)) :=
    continuous_increasing_adapted_variation hT F hF _ (fun _ _ => measurable_const)
      (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  obtain ⟨B,L,C,J,hL,hC,hJ,heC⟩ := martingale_variation_composition_covariance P hT F hF hle hnull
    W (fun _ _ => 0) A hW hz (fun _ _ _ => continuousAt_const) hA ψ hψ c hc hcm.monotone hcT hcc
  have hψd x : fderiv ℝ ψ ![x,0] (Pi.single 0 1)=deriv f (φ x)*f (φ x) := by
    have ht := ((hψ.differentiable (by norm_num)) ![x,0]).hasFDerivAt.comp_hasDerivAt x
      (fin2_time_slice_derivative x 0)
    exact ht.unique (((hf.differentiable (by norm_num)) _).hasDerivAt.comp x (hφ x))
  refine ⟨N,B,L,C,hN,hNI,hL,hC,?_⟩
  intro d hd hdT
  have hdt := real_time_below d hd hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d≤c j := by
    change (realTimeClamp d:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact (EReal.coe_lt_coe_iff.mp hj).le
  have hJi := clock_variation_integral_at_time P A J _ c hc hcT hcl hJ j d hd hdj
  filter_upwards [hIto,heC,hJi] with w hi hcw hjw
  have hcid : C (realTimeClamp d) w=∫ r in 0..d,deriv f (φ (W (realTimeClamp r) w))*f (φ (W (realTimeClamp r) w)) := by
    rw [hcw _ hdt,hjw]
    apply intervalIntegral.integral_congr
    intro r _
    exact hψd _
  rw [hcid]
  exact hi d hd hdT

end Asakura.Chapter4
