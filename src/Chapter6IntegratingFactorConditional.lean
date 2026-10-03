import Chapter6IntegratingFactor
import Chapter6WeightedLocalConditional

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Divide the conditional weighted identity by the positive adapted
integrating factor, obtaining exactly the displayed BSDE formula. -/
theorem integrating_factor_conditional_formula {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (α φ : ℝ → Ω → ℝ) (hα : ∀ w,Continuous (fun r => α r w))
    (A : ℝ → Ω → ℝ) (R s K : ℝ) (hK : 0≤K) (hs : s∈Icc 0 R)
    (hαb : ∀ w r,r∈Icc 0 R → |α r w|≤K)
    (hA : ∀ w r,r∈Icc 0 R → A r w=linearIntegratingFactor (fun u => α u w) r)
    (hAs : Measurable[G] (A s)) (ξ Y : Ω → ℝ)
    (hi : Integrable (fun w => ξ w*A R w+∫ r in s..R,A r w*φ r w) P)
    (he : P[(fun w => ξ w*A R w+∫ r in s..R,A r w*φ r w)|G]=ᵐ[P] fun w => Y w*A s w) :
    P[(fun w => ξ w*Real.exp (∫ r in s..R,α r w)+
      ∫ r in s..R,φ r w*Real.exp (∫ u in s..r,α u w))|G]=ᵐ[P] Y := by
  have hAp w : 0<A s w := by rw [hA w s hs]; exact Real.exp_pos _
  have hib : ∀ᵐ w ∂P,‖(A s w)⁻¹‖≤(Real.exp (-K*R))⁻¹ := by
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hAp w))]
    apply inv_anti₀ (Real.exp_pos _)
    rw [hA w s hs]
    exact (integrating_factor_bounds _ K R hK (hαb w) s hs).1
  have hh := condExp_stronglyMeasurable_mul_of_bound hG hAs.inv.stronglyMeasurable hi _ hib
  have heq : (fun w => (A s w)⁻¹*(ξ w*A R w+∫ r in s..R,A r w*φ r w))=
      (fun w => ξ w*Real.exp (∫ r in s..R,α r w)+∫ r in s..R,φ r w*Real.exp (∫ u in s..r,α u w)) := by
    funext w
    rw [mul_add,← intervalIntegral.integral_const_mul]
    have hrati r (hr : r∈Icc 0 R) : A r w/A s w=Real.exp (∫ u in s..r,α u w) := by
      rw [hA w r hr,hA w s hs]
      exact integrating_factor_ratio _ (hα w) s r
    have ht : (A s w)⁻¹*(ξ w*A R w)=ξ w*Real.exp (∫ r in s..R,α r w) := by
      rw [← hrati R ⟨hs.1.trans hs.2,le_rfl⟩]
      ring
    rw [ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.2] at hr
    dsimp only
    rw [← hrati r ⟨hs.1.trans hr.1,hr.2⟩]
    ring
  change P[(fun w => (A s w)⁻¹*(ξ w*A R w+∫ r in s..R,A r w*φ r w))|G]=ᵐ[P] _ at hh
  rw [heq] at hh
  filter_upwards [hh,he] with w hh he
  change P[(fun w => ξ w*Real.exp (∫ r in s..R,α r w)+∫ r in s..R,φ r w*Real.exp (∫ u in s..r,α u w))|G] w=
    (A s w)⁻¹*P[(fun w => ξ w*A R w+∫ r in s..R,A r w*φ r w)|G] w at hh
  rw [hh,he]
  field_simp [(hAp w).ne']

end Asakura.Chapter6
