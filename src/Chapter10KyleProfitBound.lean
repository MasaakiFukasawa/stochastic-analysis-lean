import FullAuditKyleProfitExercise

open MeasureTheory Filter
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Conditioning the actual Ito profit identity leaves a nonnegative terminal
loss. The payoff and stochastic-integral increment are separate hypotheses. -/
theorem kyle_conditional_profit_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ m)
    (V pT Z profit : Ω → ℝ) (p₀ l σ T : ℝ) (hl : 0<l)
    (hV : StronglyMeasurable[G] V) (hV2 : MemLp V 2 P) (hpT2 : MemLp pT 2 P)
    (hZ : Integrable Z P) (hzero : P[Z | G] =ᵐ[P] 0)
    (hprofit : profit =ᵐ[P] (fun w =>
      ((V w-p₀)^2-(V w-pT w)^2)/(2*l)+l*σ^2*T/2-σ*Z w)) :
    P[profit | G] ≤ᵐ[P] (fun w => (V w-p₀)^2/(2*l)+l*σ^2*T/2) := by
  letI : MeasurableSpace Ω := m
  let A := fun w => (V w-p₀)^2/(2*l)+l*σ^2*T/2
  let L := fun w => (V w-pT w)^2/(2*l)
  have hA : Integrable A P :=
    (((memLp_two_iff_integrable_sq (hV2.sub (memLp_const p₀)).aestronglyMeasurable).mp
      (hV2.sub (memLp_const p₀))).div_const _).add (integrable_const _)
  have hL : Integrable L P :=
    ((memLp_two_iff_integrable_sq (hV2.sub hpT2).aestronglyMeasurable).mp
      (hV2.sub hpT2)).div_const _
  have hmA : StronglyMeasurable[G] A :=
    (((hV.measurable.sub_const p₀).pow_const 2).div_const _ |>.add_const _).stronglyMeasurable
  have he : profit =ᵐ[P] A-L-σ • Z := by
    filter_upwards [hprofit] with w hw
    rw [hw]
    simp only [A,L,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hc := condExp_congr_ae (m := G) he
  have hs := condExp_sub (hA.sub hL) (hZ.smul σ) G
  have hs' := condExp_sub hA hL G
  have hz := condExp_smul σ Z G (μ := P)
  have hn : 0 ≤ᵐ[P] P[L | G] := condExp_nonneg
    (Eventually.of_forall fun w => div_nonneg (sq_nonneg _) (by positivity))
  have ha := condExp_of_stronglyMeasurable hG hmA hA
  filter_upwards [hc,hs,hs',hz,hzero,hn] with w hc hs hs' hz hzero hn
  change P[profit | G] w ≤ A w
  rw [hc,hs]
  simp only [Pi.sub_apply,hs',ha,hz,Pi.smul_apply,hzero,Pi.zero_apply,smul_zero,sub_zero]
  exact sub_le_self _ hn

end Asakura.Chapter10
