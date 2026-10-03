import Chapter4VectorCoefficientEnergy
import Chapter4VectorPrefixMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma one_coefficient_difference_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {dim : ℕ}
    (R L : ℝ) (hR : 0≤R) (hL : 0≤L)
    (b : (Fin dim → ℝ) → ℝ) (hb : Continuous b)
    (hLip : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable Y₁) (hm₂ : Measurable Y₂) (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P) :
    let U := fun z : Ω × ℝ => b (Y₁ z.1 (projIcc 0 R hR z.2))-b (Y₂ z.1 (projIcc 0 R hR z.2))
    MemLp U 2 (P.prod (volume.restrict (Ioc (0:ℝ) R))) ∧
      (∫ z,U z^2 ∂P.prod (volume.restrict (Ioc (0:ℝ) R)))≤
        L*(∫ r in 0..R,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P)) := by
  dsimp only
  obtain ⟨_,hiU,_,hE⟩ := coefficient_difference_energy P R L hR hL b (fun _ => 0) hb continuous_const
    (by simpa only [sub_self,zero_pow (by decide : (2:ℕ)≠0),add_zero] using hLip) Y₁ Y₂ hm₁ hm₂ hi₁ hi₂
  simp only [sub_self,zero_pow (by decide : (2:ℕ)≠0),add_zero] at hE
  refine ⟨hiU,hE.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (time_energy_le_prefix_moment P hR (fun w => Y₁ w-Y₂ w) (hm₁.sub hm₂) (hi₁.sub hi₂)) hL

end Asakura.Chapter4.Vector
