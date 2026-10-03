import Chapter7BrownianProjectionLaw
import Chapter4DeterministicItoEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma brownian_projection_second {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (u : Fin d → ℝ) :
    let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    MemLp X 2 P ∧ (∫ w,X w^2 ∂P)=(t-s)*(∑ i,u i^2) := by
  have h := (brownian_projection_law P B s t hs hst u).1
  exact ⟨h.memLp (memLp_id_gaussianReal 2),by
    simpa only [NNReal.toReal,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] using gaussian_law_square_integral P _ 0 _ h⟩

lemma brownian_projection_cross {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (u v : Fin d → ℝ) :
    let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    let Y := fun w => ∑ i,v i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
    Integrable (fun w => X w*Y w) P ∧
    (∫ w,X w*Y w ∂P)=(t-s)*(∑ i,u i*v i) := by
  classical
  dsimp only
  let X := fun w => ∑ i,u i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
  let Y := fun w => ∑ i,v i*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w)
  have hx := brownian_projection_second P B s t hs hst u
  have hy := brownian_projection_second P B s t hs hst v
  have hxy := brownian_projection_second P B s t hs hst (fun i => u i+v i)
  have hX2 : Integrable (fun w => X w^2) P := (memLp_two_iff_integrable_sq hx.1.aestronglyMeasurable).mp hx.1
  have hY2 : Integrable (fun w => Y w^2) P := (memLp_two_iff_integrable_sq hy.1.aestronglyMeasurable).mp hy.1
  have hXY : Integrable (fun w => X w*Y w) P := hx.1.integrable_mul hy.1
  refine ⟨hXY,?_⟩
  have hp w : (∑ i,(u i+v i)*(B.W i (realTimeClamp t) w-B.W i (realTimeClamp s) w))^2 =
      X w^2+Y w^2+2*(X w*Y w) := by
    simp only [add_mul,Finset.sum_add_distrib]
    change (X w+Y w)^2=_
    ring
  have hint := hxy.2
  simp_rw [hp] at hint
  have hi2 : Integrable (fun w => 2*(X w*Y w)) P := hXY.const_mul 2
  have hiadd : Integrable (fun w => X w^2+Y w^2) P := hX2.add hY2
  rw [integral_add hiadd hi2,integral_add hX2 hY2,integral_const_mul,hx.2,hy.2] at hint
  have hq : (∑ i,(u i+v i)^2)=(∑ i,u i^2)+(∑ i,v i^2)+2*(∑ i,u i*v i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hq] at hint
  dsimp only [X,Y] at hint ⊢
  linarith

end Asakura.Chapter7
