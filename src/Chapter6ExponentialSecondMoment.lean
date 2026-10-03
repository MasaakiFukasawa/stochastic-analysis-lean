import Chapter6NovikovWritten
import Chapter6BoundedClockExponential

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The L2 bound on the actual Girsanov density, from Novikov applied to
2Z and the bound on its unscaled quadratic variation. -/
theorem exponential_density_second_moment {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w≤t}) (hτt : ∀ w,τ w<⊤)
    (K : ℝ) (hK : ∀ᵐ w ∂P,C (τ w) w≤K) :
    let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
    MemLp D 2 P ∧ (∫ w,(D w)^2 ∂P)≤Real.exp K := by
  let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
  have hz := (open_process_stopped_regular F hF Z (hZ.adapted P F) (hZ.path P F) τ hτ hτt).1 ⊤
  have hc := (hC.stopped_regular P F hF hle hZ hZ τ hτ hτt).1 ⊤
  simp only [min_top_right] at hz hc
  have hDm : Measurable D := (((hz.mono (hle _) le_rfl).sub ((hc.mono (hle _) le_rfl).div_const 2)).exp)
  have hi := exponential_integrable_of_upper_bound P (fun w => 4*C (τ w) w)
    (measurable_const.mul (hc.mono (hle _) le_rfl)) (4*K) 1 (by norm_num)
    (hK.mono (fun w hw => mul_le_mul_of_nonneg_left hw (by norm_num)))
  obtain ⟨hi2,_,hm2,_⟩ := novikov_written P hT F hF hle hnull
    (fun t w => 2*Z t w) (fun t w => 2^2*C t w) (hZ.smul P F 2)
    (scaled_self_covariance P F Z C hC 2) τ hτ hτt 1 (by norm_num) (by norm_num at hi ⊢; exact hi)
  let E := fun w => Real.exp (2*Z (τ w) w-2*C (τ w) w)
  have hEi : Integrable E P := by
    convert hi2 ⊤ using 1
    funext w
    simp only [min_top_right,E]
    congr 1
    ring
  have hEm : (∫ w,E w ∂P)=1 := by
    convert hm2 using 1
    congr 1
    funext w
    simp only [min_top_right,E]
    congr 1
    ring
  have hb : ∀ᵐ w ∂P,D w^2≤Real.exp K*E w := by
    filter_upwards [hK] with w hw
    dsimp only [D,E]
    rw [sq,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hD2i : Integrable (fun w => D w^2) P :=
    (hEi.const_mul (Real.exp K)).mono' (hDm.pow_const 2).aestronglyMeasurable
      (hb.mono (fun w hw => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (D w))] using hw))
  refine ⟨(memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).mpr hD2i,?_⟩
  calc
    _ ≤ ∫ w,Real.exp K*E w ∂P := integral_mono_ae hD2i (hEi.const_mul _) hb
    _ = Real.exp K := by rw [integral_const_mul,hEm,mul_one]

end Asakura.Chapter6
