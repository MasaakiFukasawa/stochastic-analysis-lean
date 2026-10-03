import Chapter6ConditionalYoungBound

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem linear_growth_memLp_two {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → E) (b : E → F)
    (hU : MemLp U 2 P) (hb : AEStronglyMeasurable (b ∘ U) P)
    (K : ℝ) (hbound : ∀ x,‖b x‖≤K*(1+‖x‖)) : MemLp (b ∘ U) 2 P := by
  have hh : MemLp (fun w => K*(1+‖U w‖)) 2 P := ((memLp_const (1:ℝ)).add hU.norm).const_mul K
  exact hh.mono' hb (ae_of_all _ (fun w => hbound _))

theorem conditional_linear_growth_square {Ω E F : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → E) (b : E → F)
    (hU : MemLp U 2 P) (hb : AEStronglyMeasurable (b ∘ U) P)
    (K : ℝ) (hK : 0≤K) (hbound : ∀ x,‖b x‖≤K*(1+‖x‖))
    (G : MeasurableSpace Ω) (hG : G≤m) :
    ∀ᵐ w ∂P,P[(fun w => ‖b (U w)‖^2)|G] w≤2*K^2*(1+P[(fun w => ‖U w‖^2)|G] w) := by
  letI : MeasurableSpace Ω := m
  have hb2 := linear_growth_memLp_two P U b hU hb K hbound
  have hui := hU.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hbi := hb2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hp w : ‖b (U w)‖^2≤2*K^2*(1+‖U w‖^2) := by
    have hh := hbound (U w)
    have hsq : ‖b (U w)‖^2≤(K*(1+‖U w‖))^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg (‖U w‖-1))]
  have hm := condExp_mono (m := G) hbi (((integrable_const (1:ℝ)).add hui).const_mul (2*K^2)) (ae_of_all _ hp)
  have hs := condExp_smul (μ := P) (2*K^2) (fun w => 1+‖U w‖^2) G
  have ha := condExp_add (integrable_const (1:ℝ)) hui G
  have hc : P[(fun _ : Ω => (1:ℝ))|G]=fun _ => 1 := condExp_of_stronglyMeasurable hG stronglyMeasurable_const (integrable_const _)
  filter_upwards [hm,hs,ha] with w hm hs ha
  change P[(fun w => 2*K^2*(1+‖U w‖^2))|G] w=2*K^2*P[(fun w => 1+‖U w‖^2)|G] w at hs
  change P[(fun w => 1+‖U w‖^2)|G] w=P[(fun _ : Ω => (1:ℝ))|G] w+P[(fun w => ‖U w‖^2)|G] w at ha
  change P[(fun w => ‖b (U w)‖^2)|G] w≤P[(fun w => 2*K^2*(1+‖U w‖^2))|G] w at hm
  rw [hs,ha,hc] at hm
  exact hm

end Asakura.Chapter6
