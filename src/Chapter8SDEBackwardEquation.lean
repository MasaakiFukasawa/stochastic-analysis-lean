import Chapter8SDEGeneratorInterface
import Chapter4LipschitzSemigroup

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual SDE semigroup and the proved right-generator formula
give the backward equation. No generator-commutation identity is assumed. -/
theorem sde_backward_equation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W b σ (fun _ => x) (Z x))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (K : ℝ) (hb : ∀ y,‖f y‖≤K)
    (deg : ℕ) (C : ℝ) (hC : 0≤C)
    (hfb : ∀ y,|f y|≤C*(1+(Real.sqrt (∑ i,y i^2))^deg))
    (hgb : ∀ y,|coordinateGenerator b σ f y|≤C*(1+(Real.sqrt (∑ i,y i^2))^deg))
    (t : ℝ) (ht : 0<t)
    (hc2 : ContDiff ℝ 2 (fun x => ∫ w,f (Z x (realTimeClamp t) w) ∂P))
    (deg' : ℕ) (C' : ℝ) (hC' : 0≤C')
    (hfb' : ∀ y,|∫ w,f (Z y (realTimeClamp t) w) ∂P|≤C'*(1+(Real.sqrt (∑ i,y i^2))^deg'))
    (hgb' : ∀ y,|coordinateGenerator b σ (fun x => ∫ w,f (Z x (realTimeClamp t) w) ∂P) y|
      ≤C'*(1+(Real.sqrt (∑ i,y i^2))^deg')) (x : Fin d → ℝ) :
    HasDerivAt (fun r => ∫ w,f (Z x (realTimeClamp r) w) ∂P)
      (coordinateGenerator b σ (fun y => ∫ w,f (Z y (realTimeClamp t) w) ∂P) x) t := by
  obtain ⟨hbc,hσc,_,_⟩ := Vector.manuscript_lipschitz_coordinates b σ L hL hLip
  have hd := (sde_generator_formulas P B b σ L hL hLip x (Z x) (hZ x) f hf
    (coordinate_generator_continuous b σ hbc hσc f hf) deg C hC hfb hgb).2 t ht
  let G := fun r x => ∫ w,f (Z x (realTimeClamp r) w) ∂P
  let Q := fun r (g : (Fin d → ℝ) → ℝ) x => ∫ w,g (Z x (realTimeClamp r) w) ∂P
  have hz := (sde_generator_formulas P B b σ L hL hLip x (Z x) (hZ x) (G t) hc2
    (coordinate_generator_continuous b σ hbc hσc (G t) hc2) deg' C' hC' hfb' hgb').1
  have hsemi (h : ℝ) (hh : 0≤h) : Q h (G t) x=G (t+h) x := by
    have he := congrFun (lipschitz_transition_semigroup P B L hL b σ hLip Z hZ
      f hf.continuous.measurable K hb ⟨h,hh⟩ ⟨t,ht.le⟩) x
    change G (h+t) x=Q h (G t) x at he
    rw [add_comm h t] at he
    exact he.symm
  have he := semigroup_backward_generator Q G (coordinateGenerator b σ) t x _ hd hz hsemi
  rw [he]
  exact hd

end Asakura.Chapter8
