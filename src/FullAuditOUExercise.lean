import FullAuditGaussianIBP

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.FullAudit
set_option maxHeartbeats 500000

/-- Differentiate the actual invariant Gaussian log density; the score is
 obtained from its density, not inserted as an assumption. -/
theorem stationary_gaussian_score (x : ℝ) :
    HasDerivAt (fun y => Real.log (gaussianPDFReal 0 1 y)) (-x) x := by
  have hd := gaussian_density_derivative 0 1 (by norm_num) x
  have hp := gaussianPDFReal_pos 0 1 x (by norm_num)
  have h := hd.log (ne_of_gt hp)
  convert h using 1
  norm_num only [NNReal.coe_one,sub_zero,div_one]
  field_simp

theorem ou_potential_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ => y^2/2) x x := by
  convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;> simp <;> ring

theorem ou_reverse_and_flow_drifts (x : ℝ) :
    -(-deriv (fun y : ℝ => y^2/2) x)+2*deriv (fun y => Real.log (gaussianPDFReal 0 1 y)) x = -x ∧
    -deriv (fun y : ℝ => y^2/2) x-(2:ℝ)/2*deriv (fun y => Real.log (gaussianPDFReal 0 1 y)) x = 0 := by
  rw [(stationary_gaussian_score x).deriv,(ou_potential_derivative x).deriv]
  constructor <;> ring

/-- The OU transition preserves the actual standard normal law, by summing
 its independent Gaussian initial and innovation terms. -/
theorem ou_stationary_transition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Z : Ω → ℝ) (hX : HasLaw X (gaussianReal 0 1) P) (hZ : HasLaw Z (gaussianReal 0 1) P)
    (hXZ : IndepFun X Z P) (t : ℝ) (ht : 0 ≤ t) :
    HasLaw (fun ω => Real.exp (-t)*X ω+Real.sqrt (1-Real.exp (-2*t))*Z ω) (gaussianReal 0 1) P := by
  let a := Real.exp (-t)
  let b := Real.sqrt (1-Real.exp (-2*t))
  have hvar : 0 ≤ 1-Real.exp (-2*t) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have he : a^2+b^2 = 1 := by
    dsimp [a,b]
    rw [Real.sq_sqrt hvar,pow_two,← Real.exp_add]
    rw [show -t + -t = -2*t by ring]
    ring
  have hA := gaussianReal_const_mul hX a
  have hB := gaussianReal_const_mul hZ b
  have hind : IndepFun (fun ω => a*X ω) (fun ω => b*Z ω) P :=
    hXZ.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hA hB
  have hv : (⟨a^2,sq_nonneg a⟩ : ℝ≥0)*1+⟨b^2,sq_nonneg b⟩*1 = 1 := by
    apply Subtype.ext
    change a^2*1+b^2*1 = (1:ℝ)
    simpa only [mul_one] using he
  refine ⟨hA.aemeasurable.add hB.aemeasurable,?_⟩
  change P.map ((fun ω => a*X ω)+(fun ω => b*Z ω)) = gaussianReal 0 1
  rw [hsum]
  congr 1
  · simp only [mul_zero,zero_add]

/-- The probability-flow solution is the constant path; with Gaussian
 initial data it has the same stationary one-time laws. -/
theorem ou_probability_flow_stationary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : HasLaw X (gaussianReal 0 1) P) :
    (∀ (ω : Ω) (t : ℝ), HasDerivAt (fun _ : ℝ => X ω) 0 t) ∧
      (∀ t : ℝ, HasLaw (fun ω => X ω) (gaussianReal 0 1) P) := by
  exact ⟨fun ω t => hasDerivAt_const t (X ω),fun _ => hX⟩

end Asakura.FullAudit
