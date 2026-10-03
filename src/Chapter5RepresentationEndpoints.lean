import Chapter2M2ProcessRepresentatives

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

/-- The martingale increment has conditional mean zero at its left end.
Continuity of the original martingale is not required. -/
theorem martingale_increment_conditional_zero
    {Ω I : Type*} {m : MeasurableSpace Ω} [Preorder I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : I → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (Y : I → Ω → ℝ) (hYm : ∀ t,Measurable[F t] (Y t))
    (hYi : ∀ t,Integrable (Y t) P)
    (hY : ∀ s t,s ≤ t → P[Y t|F s] =ᵐ[P] Y s)
    (a b : I) (hab : a ≤ b) :
    P[(fun w => Y b w-Y a w)|F a] =ᵐ[P] 0 := by
  have hh := condExp_sub (m := F a) (hYi b) (hYi a)
  rw [condExp_of_stronglyMeasurable (hle a) (hYm a).stronglyMeasurable (hYi a)] at hh
  filter_upwards [hh,hY a b hab] with w hw hm
  simpa only [Pi.sub_def,Pi.sub_apply,hm,sub_self,Pi.zero_apply] using hw

/-- A terminal integral representation of an increment yields the two
endpoint identities needed to restrict its integrand to that interval. -/
theorem representation_increment_endpoints
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (M : ClosedTime T → Ω → ℝ) (hM : ContinuousM2Witness P F M)
    (a b : ClosedTime T) (ξ : Ω → ℝ) (hξi : Integrable ξ P)
    (hξm : Measurable[F b] ξ) (hξ0 : P[ξ|F a] =ᵐ[P] 0)
    (hterminal : M ⊤ =ᵐ[P] ξ) :
    M a =ᵐ[P] 0 ∧ M b =ᵐ[P] ξ := by
  constructor
  · exact (hM.martingale a ⊤ le_top).symm.trans ((condExp_congr_ae hterminal).trans hξ0)
  · have hh := (hM.martingale b ⊤ le_top).symm.trans (condExp_congr_ae hterminal)
    rw [condExp_of_stronglyMeasurable (hle b) hξm.stronglyMeasurable hξi] at hh
    exact hh

end Asakura.Chapter5
