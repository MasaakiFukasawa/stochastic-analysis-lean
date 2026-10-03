import FullAuditBrownianMartingaleExercise
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianExponential {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (σ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (σ*B t ω-σ^2*(t:ℝ)/2)

/-- Integrability and mean of the actual normalized Gaussian exponential. -/
theorem normalized_gaussian_exponential {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) P) (σ : ℝ) :
    Integrable (fun ω => Real.exp (σ*X ω-σ^2*(v:ℝ)/2)) P ∧
      (∫ ω, Real.exp (σ*X ω-σ^2*(v:ℝ)/2) ∂P) = 1 := by
  have hi : Integrable (fun ω => Real.exp (σ*X ω)) P :=
    hX.integrable_comp (integrable_exp_mul_gaussianReal σ)
  have he : (fun ω => Real.exp (σ*X ω-σ^2*(v:ℝ)/2)) =
      fun ω => Real.exp (-(σ^2*(v:ℝ)/2))*Real.exp (σ*X ω) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul]
  have hm := mgf_gaussianReal hX σ
  change (∫ ω, Real.exp (σ*X ω) ∂P) = _ at hm
  rw [hm,zero_mul,zero_add,← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

/-- The Gaussian increment factor is independent of the entire past. -/
theorem brownian_exponential_martingale {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable[m] (B t))
    (σ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    P[brownianExponential B σ t | pastSigma B s] =ᵐ[P] brownianExponential B σ s := by
  let H := MeasurableSpace.comap (fun ω (r : Iic s) => B r.val ω) inferInstance
  letI : MeasurableSpace Ω := m
  let v := nndist (t:ℝ) (s:ℝ)
  let I := fun ω => Real.exp (σ*(B t ω-B s ω)-σ^2*(v:ℝ)/2)
  have hv : (v:ℝ) = (t:ℝ)-(s:ℝ) := by
    dsimp [v]
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst))]
  have hI := normalized_gaussian_exponential P (fun ω => B t ω-B s ω) v (hB.hasLaw_sub t s) σ
  have hZt := (normalized_gaussian_exponential P (B t) t (hB.hasLaw_eval t) σ).1
  have hind : IndepFun I (fun ω (r : Iic s) => B r.val ω) P := by
    have h := (hB.indepFun_shift s).comp (measurable_pi_apply (t-s)) measurable_id
    have hd : IndepFun (fun ω => B t ω-B s ω) (fun ω (r : Iic s) => B r.val ω) P := by
      simpa only [Function.comp_def,id_eq,add_tsub_cancel_of_le hst] using h
    exact hd.comp (by fun_prop : Measurable (fun x : ℝ => Real.exp (σ*x-σ^2*(v:ℝ)/2))) measurable_id
  have hIm : Measurable[m] I := by dsimp [I]; fun_prop
  have hH : H ≤ m := (Measurable.of_eval (fun r : Iic s => hm r.val)).comap_le
  have hCE : P[I | H] =ᵐ[P] (fun _ => (1:ℝ)) := by
    have h := condExp_indep_eq hIm.comap_le hH
      (show StronglyMeasurable[MeasurableSpace.comap I inferInstance] I from
        (Measurable.of_comap_le le_rfl).stronglyMeasurable) hind
    have hmean : (∫ ω, I ω ∂P) = 1 := hI.2
    simpa only [hmean] using h
  have hhist := past_sigma_history B s
  change pastSigma B s = H at hhist
  rw [← hhist] at hCE
  have he : brownianExponential B σ t = brownianExponential B σ s * I := by
    funext ω
    change Real.exp _ = Real.exp _*Real.exp _
    rw [← Real.exp_add,hv]
    congr 1
    ring
  have hZs : StronglyMeasurable[pastSigma B s] (brownianExponential B σ s) := by
    apply Measurable.stronglyMeasurable
    exact (((natural_process_adapted B s).const_mul σ).sub_const _).exp
  have hprod : Integrable (brownianExponential B σ s*I) P := by rwa [← he]
  have hp := condExp_mul_of_stronglyMeasurable_left hZs hprod hI.1
  rw [he]
  filter_upwards [hp,hCE] with ω hp hc
  rw [hp]
  simp only [Pi.mul_apply,hc,mul_one]

end Asakura.FullAudit
