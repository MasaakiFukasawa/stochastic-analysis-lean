import FullAuditLangevinContraction

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Contraction of a common-forcing integral equation in Euclidean
coordinates; the value of the common forcing at zero cancels as well. -/
theorem coordinate_path_contraction {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : E ≃L[ℝ] G) (g : E → E) (hg : Continuous g) (κ T : ℝ) (hT : 0≤T)
    (hm : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (X Y W : ℝ → E) (x y : E) (hcX : Continuous X) (hcY : Continuous Y)
    (hx : ∀ t∈Icc 0 T,X t=x-(∫ s in 0..t,g (X s))+W t)
    (hy : ∀ t∈Icc 0 T,Y t=y-(∫ s in 0..t,g (Y s))+W t) :
    ∀ t∈Icc 0 T,‖e (X t)-e (Y t)‖≤Real.exp (-κ*t)*‖e x-e y‖ := by
  let G := fun z => e (g (e.symm z))
  have hmono a b : κ*‖a-b‖^2≤⟪a-b,G a-G b⟫ := by
    simpa only [G,e.apply_symm_apply] using hm (e.symm a) (e.symm b)
  have hd := langevin_common_noise_difference X Y W g x y T hcX hcY hg hx hy
  have hdE t (ht : t∈Ioo 0 T) : HasDerivAt (fun s => e (X s)-e (Y s))
      (-(G (e (X t))-G (e (Y t)))) t := by
    simpa only [G,e.symm_apply_apply,Function.comp_def,map_sub,map_neg,ContinuousLinearEquiv.coe_coe] using
      e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hzero : e (X 0)-e (Y 0)=e x-e y := by
    rw [hx 0 ⟨le_rfl,hT⟩,hy 0 ⟨le_rfl,hT⟩]
    simp only [intervalIntegral.integral_same,sub_zero,map_add]
    abel
  intro t ht
  have hh := langevin_path_contraction (fun s => e (X s)) (fun s => e (Y s)) G κ T hT
    (e.continuous.comp hcX).continuousOn (e.continuous.comp hcY).continuousOn hmono hdE t ht
  rwa [hzero] at hh

end Asakura.Chapter8
