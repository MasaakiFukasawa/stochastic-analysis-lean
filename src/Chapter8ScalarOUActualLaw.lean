import Chapter8ScalarEinsteinExercise
import Chapter8SDEAdditiveEquation
import Chapter8AdditiveUniqueness
import Chapter8BrownianForcingPath

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Identify an actual scalar SDE solution with the already constructed
OU solution, so its Gaussian transition law can be used in inference. -/
theorem scalar_ou_actual_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ σ x : ℝ) (hθ : 0<θ)
    (X : HalfClosedTime → Ω → Fin 1 → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun _ y => -θ*y 0) (fun _ _ _ => σ) (fun _ _ => x) X)
    (T : ℝ) (hT : 0≤T) :
    HasLaw (fun w => X (realTimeClamp T) w 0) (ouKernel θ σ hθ ⟨T,hT⟩ x) P := by
  obtain ⟨N,hN,hNI,he,hl⟩ := ou_solution_and_transition_law P (T := ⊤) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w r hr _ => B.diagonal_clock 0 w r hr) θ σ x hθ
  apply (hl T hT (EReal.coe_lt_top _)).congr
  filter_upwards [he,sde_additive_equation P B (fun _ y => -θ*y 0) (fun _ _ => σ)
    (fun _ => x) X hX] with w hw hx
  have hcX : Continuous (fun r : ℝ => X (realTimeClamp r) w 0) := by
    apply (continuous_apply 0).comp
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hcN : Continuous (fun r : ℝ => N (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((hN.path P B.F) w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hcY : Continuous (fun r : ℝ => Real.exp (-θ*r)*(x+N (realTimeClamp r) w)) :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (-θ*r))).mul (continuous_const.add hcN)
  have h1 r (hr : r∈Icc 0 T) : X (realTimeClamp r) w 0=x+
      (∫ s in 0..r,-θ*X (realTimeClamp s) w 0)+σ*B.W 0 (realTimeClamp r) w := by
    simpa only [Fin.sum_univ_one] using hx r hr.1 0
  have h2 r (hr : r∈Icc 0 T) : Real.exp (-θ*r)*(x+N (realTimeClamp r) w)=x+
      (∫ s in 0..r,-θ*(Real.exp (-θ*s)*(x+N (realTimeClamp s) w)))+σ*B.W 0 (realTimeClamp r) w := by
    rw [intervalIntegral.integral_const_mul]
    simpa only [neg_mul,sub_eq_add_neg] using hw r hr.1 (EReal.coe_lt_top _)
  have hu := additive_path_unique (fun y : ℝ => -θ*y) ‖-θ‖₊
    (by simpa only [smul_eq_mul] using (lipschitzWith_smul (-θ) : LipschitzWith ‖-θ‖₊ (fun y : ℝ => (-θ) • y))) _ _ (fun r => σ*B.W 0 (realTimeClamp r) w)
    hcX hcY x T hT h1 h2 T ⟨hT,le_rfl⟩
  exact hu
end Asakura.Chapter8
