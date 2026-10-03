import Chapter4ConditionalCharacteristicLaw
import Chapter4BrownianCharacterization

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter9
open Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The conditional characteristic identity gives the joint Gaussian
 increment (all projections) and independence of the entire past. -/
theorem brownian_increment_law {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (G : MeasurableSpace Ω) (hG : G≤m) (Y : Ω → Fin d → ℝ) (hY : Measurable[m] Y)
    (δ : ℝ) (hδ : 0≤δ)
    (hchar : ∀ v : Fin d → ℝ,
      P[(fun w => Complex.exp (((∑ i,v i*Y w i):ℝ)*Complex.I))|G]=ᵐ[P]
        fun _ => Complex.exp (-((δ*(∑ i,(v i)^2):ℝ):ℂ)/2)) :
    (∀ v : Fin d → ℝ,HasLaw (fun w => ∑ i,v i*Y w i)
      (gaussianReal 0 ⟨δ*(∑ i,(v i)^2),mul_nonneg hδ (Finset.sum_nonneg fun i _ => sq_nonneg (v i))⟩) P) ∧
    Indep (MeasurableSpace.comap Y inferInstance) G P := by
  letI : MeasurableSpace Ω := m
  constructor
  · intro v
    have hm : Measurable (fun w => ∑ i,v i*Y w i) := by
      apply Finset.measurable_sum
      intro i _
      exact measurable_const.mul ((measurable_pi_apply i).comp hY)
    apply (gaussian_independent_of_conditional_characteristic P G hG _ hm _ ?_).1
    intro u
    have hh := hchar (fun i => u*v i)
    have he w : (∑ i,(u*v i)*Y w i)=u*(∑ i,v i*Y w i) := by
      simp only [mul_assoc,Finset.mul_sum]
    have hv : δ*(∑ i,(u*v i)^2)=(δ*(∑ i,(v i)^2))*u^2 := by
      simp only [mul_pow,← Finset.mul_sum]
      ring
    simp only [he,hv,Complex.ofReal_mul,Complex.ofReal_pow] at hh
    convert hh using 1
    funext w
    congr 1
    change -((δ*(∑ i,(v i)^2):ℝ):ℂ)*(u:ℂ)^2/2= _
    push_cast
    ring
  · let K := fun L : StrongDual ℝ (Fin d → ℝ) =>
      Complex.exp (-((δ*(∑ i,(L (Pi.single i 1))^2):ℝ):ℂ)/2)
    apply (independence_of_constant_conditional_characteristic P G hG Y hY K ?_).2
    intro L
    have he : (fun w => Complex.exp ((L (Y w):ℂ)*Complex.I))=
        (fun w => Complex.exp (((∑ i,L (Pi.single i 1)*Y w i):ℝ)*Complex.I)) := by
      funext w
      rw [dual_coordinate_expansion]
    rw [he]
    exact hchar (fun i => L (Pi.single i 1))
end Asakura.Chapter9
