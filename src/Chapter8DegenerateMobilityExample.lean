import Chapter8FrozenCoordinateInvariant
import Chapter8ScalarEinsteinExercise
import Mathlib.LinearAlgebra.Matrix.Notation

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal Matrix
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000

/-- The example's exact Einstein matrix relation, including the frozen
direction and the prescribed positive temperature. -/
theorem degenerate_mobility_einstein (β : ℝ) (hβ : 0<β) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]
    let σ : Matrix (Fin 2) (Fin 2) ℝ := !![Real.sqrt (2*β⁻¹),0;0,0]
    σ*σᵀ=(2*β⁻¹) • M := by
  dsimp only
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,←pow_two,mul_pow,inv_pow,Real.sq_sqrt hβ.le]

/-- The unchanged coordinate permits every probability law, rather than
only the Gibbs Gaussian. Thus the example really has nonunique invariant laws. -/
theorem degenerate_mobility_invariant (β : ℝ) (hβ : 0<β) (t : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (((gaussianReal 0 ⟨β⁻¹,by positivity⟩).prod ν).prod
      (gaussianReal 0 (Asakura.FullAudit.ouVariance 1 (Real.sqrt (2*β⁻¹)) (by norm_num) t))).map
        (fun z => (Real.exp (-(t:ℝ))*z.1.1+z.2,z.1.2))=
      (gaussianReal 0 ⟨β⁻¹,by positivity⟩).prod ν := by
  have hv : ouStationaryVariance 1 (Real.sqrt (2*β⁻¹)) (by norm_num)=⟨β⁻¹,by positivity⟩ := by
    apply NNReal.eq
    change (Real.sqrt (2*β⁻¹))^2/(2*1)=β⁻¹
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hh := frozen_ou_product_invariant 1 (Real.sqrt (2*β⁻¹)) (by norm_num) t ν
  simpa only [hv,neg_mul,one_mul] using hh

theorem degenerate_mobility_distinct_invariant_laws (β : ℝ) (hβ : 0<β) :
    (gaussianReal 0 ⟨β⁻¹,by positivity⟩).prod (Measure.dirac (0:ℝ))≠
      (gaussianReal 0 ⟨β⁻¹,by positivity⟩).prod (Measure.dirac (1:ℝ)) := by
  let v : ℝ≥0 := ⟨β⁻¹,inv_nonneg.mpr hβ.le⟩
  have hp : IsProbabilityMeasure (gaussianReal (0:ℝ) v) := inferInstance
  exact @frozen_coordinate_nonunique (gaussianReal 0 v) hp

/-- Construct the first coordinate by its Ito integral; the second is
constant. The resulting actual transition law is the Gaussian kernel
used in the invariant-product calculation above. -/
theorem degenerate_mobility_actual_dynamics {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 2)
    (β : ℝ) (hβ : 0<β) (x : Fin 2 → ℝ) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => Real.sqrt (2*β⁻¹)*Real.exp z.2) N ∧
      let Y := fun t w => ![Real.exp (-t)*(x 0+N (realTimeClamp t) w),x 1]
      (∀ᵐ w ∂P,∀ t≥0,Y t w 0=x 0-(∫ s in 0..t,Y s w 0)+Real.sqrt (2*β⁻¹)*B.W 0 (realTimeClamp t) w) ∧
      (∀ t w,Y t w 1=x 1) ∧
      (∀ (t : ℝ) (ht : 0≤t),HasLaw (Y t)
        ((ouKernel 1 (Real.sqrt (2*β⁻¹)) (by norm_num) ⟨t,ht⟩ (x 0)).map
          (fun v => ![v,x 1])) P) := by
  obtain ⟨N,hN,hNI,he,hl⟩ := ou_solution_and_transition_law P (T := ⊤) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w r hr _ => B.diagonal_clock 0 w r hr) 1 (Real.sqrt (2*β⁻¹)) (x 0) (by norm_num)
  refine ⟨N,hN,?_,?_,fun _ _ => rfl,?_⟩
  · simpa only [one_mul] using hNI
  · filter_upwards [he] with w hw
    intro t ht
    simpa only [neg_mul,one_mul,Matrix.cons_val_zero] using hw t ht (EReal.coe_lt_top t)
  · intro t ht
    have hh := hl t ht (EReal.coe_lt_top t)
    have hm : Measurable (fun v : ℝ => ![v,x 1]) := by fun_prop
    have hh' := (hasLaw_map hm.aemeasurable).comp hh
    simpa only [Function.comp_def,neg_mul,one_mul] using hh'


end Asakura.Chapter8
