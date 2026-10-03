import Chapter6ConditionalInnerBound

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem conditional_inner_young_bound {Ω E : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (b X : Ω → E)
    (hb : MemLp b 2 P) (hX : MemLp X 2 P) (q : ℝ) (hq : 0<q) (G : MeasurableSpace Ω) :
    ∀ᵐ w ∂P,|P[(fun w => ⟪b w,X w⟫_ℝ)|G] w|≤
      (q/2)*P[(fun w => ‖b w‖^2)|G] w+(1/(2*q))*P[(fun w => ‖X w‖^2)|G] w := by
  letI : MeasurableSpace Ω := m
  have hi : Integrable (fun w => ⟪b w,X w⟫_ℝ) P :=
    (hb.norm.integrable_mul hX.norm).mono' (hb.aestronglyMeasurable.inner hX.aestronglyMeasurable)
      (ae_of_all _ (fun w => norm_inner_le_norm _ _))
  have hib := hb.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hiX := hX.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hy w : |⟪b w,X w⟫_ℝ|≤(q/2)*‖b w‖^2+(1/(2*q))*‖X w‖^2 := by
    have hh := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (b w) (X w)) (show 0≤2*q by positivity)
    have hs := sq_nonneg (q*‖b w‖-‖X w‖)
    have he : (q/2)*‖b w‖^2+(1/(2*q))*‖X w‖^2=(q^2*‖b w‖^2+‖X w‖^2)/(2*q) := by field_simp
    rw [he]
    apply (le_div_iff₀ (show 0<2*q by positivity)).2
    nlinarith
  have hm := condExp_mono (m := G) hi.abs ((hib.const_mul (q/2)).add (hiX.const_mul (1/(2*q)))) (ae_of_all _ hy)
  have ha := abs_condExp_ae_le_condExp_abs (μ := P) (m := G) (fun w => ⟪b w,X w⟫_ℝ)
  have hadd := condExp_add (hib.const_mul (q/2)) (hiX.const_mul (1/(2*q))) G
  have hbsm := condExp_smul (μ := P) (q/2) (fun w => ‖b w‖^2) G
  have hxsm := condExp_smul (μ := P) (1/(2*q)) (fun w => ‖X w‖^2) G
  filter_upwards [hm,ha,hadd,hbsm,hxsm] with w hm ha hadd hbsm hxsm
  change P[(fun w => (q/2)*‖b w‖^2+(1/(2*q))*‖X w‖^2)|G] w=
    P[(fun w => (q/2)*‖b w‖^2)|G] w+P[(fun w => (1/(2*q))*‖X w‖^2)|G] w at hadd
  change P[(fun w => (q/2)*‖b w‖^2)|G] w=(q/2)*P[(fun w => ‖b w‖^2)|G] w at hbsm
  change P[(fun w => (1/(2*q))*‖X w‖^2)|G] w=(1/(2*q))*P[(fun w => ‖X w‖^2)|G] w at hxsm
  change P[(fun w => |⟪b w,X w⟫_ℝ|)|G] w ≤ P[(fun w => (q/2)*‖b w‖^2+(1/(2*q))*‖X w‖^2)|G] w at hm
  rw [hadd,hbsm,hxsm] at hm
  exact ha.trans hm

end Asakura.Chapter6
