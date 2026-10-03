import Chapter7BrownianProductEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

lemma brownian_product_fourth {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (u v : Fin d → ℝ) :
    let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    let Y := fun w => ∑ i,v i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    MemLp (fun w => X w*Y w) 2 P ∧
    (∫ w,(X w*Y w)^2 ∂P)=(t-s)^2*((∑ i,u i^2)*(∑ i,v i^2)+2*(∑ i,u i*v i)^2) := by
  classical
  dsimp only
  let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
  let Y := fun w => ∑ i,v i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
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
  exact ⟨(memLp_two_iff_integrable_sq hcross.1.aestronglyMeasurable).mpr hfour.1,hfour.2⟩

end Asakura.Chapter7
