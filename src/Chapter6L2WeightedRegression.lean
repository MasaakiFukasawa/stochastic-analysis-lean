import Chapter6WeightedConditionalRegression

open MeasureTheory Set Filter
namespace Asakura.Chapter6
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The same C5 regression identity applies to linearly growing coefficients:
L2 integrability replaces the boundedness used in the preceding proposition. -/
theorem L2_weighted_conditional_regression {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y b : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hbi : MemLp b 2 P)
    (G H : MeasurableSpace Ω) (hGH : G≤H) (hH : H≤m)
    (hb : Measurable[H] b) (he : P[X|H]=ᵐ[P] Y) :
    P[(fun w => b w*X w)|G]=ᵐ[P] P[(fun w => b w*Y w)|G] := by
  have hp := condExp_mul_of_stronglyMeasurable_left hb.stronglyMeasurable (hbi.integrable_mul hX) (hX.integrable (by norm_num))
  have hm : P[(fun w => b w*X w)|H]=ᵐ[P] fun w => b w*Y w := by
    filter_upwards [hp,he] with w hp he
    change P[(fun w => b w*X w)|H] w=b w*P[X|H] w at hp
    rw [hp,he]
  have ht := condExp_condExp_of_le hGH hH (f := fun w => b w*X w) (μ := P)
  exact ht.symm.trans (condExp_congr_ae hm)

end Asakura.Chapter6
