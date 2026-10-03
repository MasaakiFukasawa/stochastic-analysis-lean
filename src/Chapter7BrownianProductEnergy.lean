import Chapter7BrownianMixedFourth
import Chapter7BrownianSecondMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The variance of a centered product of two transformed increments,
computed from the actual Brownian second and fourth moments. -/
theorem brownian_product_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (u v : Fin d → ℝ) :
    let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    let Y := fun w => ∑ i,v i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    let a := (t-s)*(∑ i,u i*v i)
    MemLp (fun w => X w*Y w-a) 2 P ∧
    (∫ w,X w*Y w-a ∂P)=0 ∧
    (∫ w,(X w*Y w-a)^2 ∂P)=
      (t-s)^2*((∑ i,u i^2)*(∑ i,v i^2)+(∑ i,u i*v i)^2) := by
  classical
  dsimp only
  let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
  let Y := fun w => ∑ i,v i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
  let a := (t-s)*(∑ i,u i*v i)
  change MemLp (fun w => X w*Y w-a) 2 P ∧
    (∫ w,X w*Y w-a ∂P)=0 ∧
    (∫ w,(X w*Y w-a)^2 ∂P)=(t-s)^2*((∑ i,u i^2)*(∑ i,v i^2)+(∑ i,u i*v i)^2)
  have hcross := brownian_projection_cross P B s t hs hst u v
  have h4 := brownian_transformed_mixed_fourth P B ![u,v,u,v] s t hs hst
  have he w : X w*Y w*X w*Y w=(X w*Y w)^2 := by ring
  have huv : (∑ i,v i*u i)=(∑ i,u i*v i) := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hfour : Integrable (fun w => (X w*Y w)^2) P ∧
      (∫ w,(X w*Y w)^2 ∂P)=(t-s)^2*((∑ i,u i^2)*(∑ i,v i^2)+2*(∑ i,u i*v i)^2) := by
    dsimp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk] at h4
    change Integrable (fun w => X w*Y w*X w*Y w) P ∧
      (∫ w,X w*Y w*X w*Y w ∂P)=_ at h4
    simp_rw [he] at h4
    refine ⟨h4.1,?_⟩
    rw [h4.2]
    simp only [← pow_two,huv]
    ring
  have hxy : MemLp (fun w => X w*Y w) 2 P :=
    (memLp_two_iff_integrable_sq hcross.1.aestronglyMeasurable).mpr hfour.1
  have hi : Integrable (fun w => X w*Y w) P := hcross.1
  have hh : (∫ w,X w*Y w ∂P)=a := hcross.2
  refine ⟨hxy.sub (memLp_const a),?_,?_⟩
  · rw [integral_sub hi (integrable_const _),hh]
    simp
  · have heq w : (X w*Y w-a)^2=(X w*Y w)^2-2*a*(X w*Y w)+a^2 := by ring
    simp_rw [heq]
    have him : Integrable (fun w => 2*a*(X w*Y w)) P := hi.const_mul _
    have his : Integrable (fun w => (X w*Y w)^2-2*a*(X w*Y w)) P := hfour.1.sub him
    rw [integral_add his (integrable_const _),integral_sub hfour.1 him,integral_const_mul,hfour.2,hh]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    dsimp only [a]
    ring

end Asakura.Chapter7
