import Chapter7BrownianFutureProjection

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianCellIntegrand {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s e : ℝ) (z : Ω × ℝ) : ℝ :=
    (Ioc s e).indicator (fun r => ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) z.1-
      B.W j (realTimeClamp (min s (max 0 r))) z.1)) z.2

lemma brownian_cell_integrand_regular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s e : ℝ) (hs : 0≤s) :
    Measurable (brownianCellIntegrand B u s e) ∧
    (∀ b,0≤b → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => brownianCellIntegrand B u s e (z.1,z.2.val))) ∧
    (∀ b,0≤b → ∀ w,IntervalIntegrable (fun r => (brownianCellIntegrand B u s e (w,r))^2) volume 0 b) := by
  let X := fun r w => ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) w-
      B.W j (realTimeClamp (min s (max 0 r))) w)
  have hr := brownian_future_projection P B u s hs
  have he : brownianCellIntegrand B u s e =
      (Prod.snd ⁻¹' Ioc s e).indicator (fun z : Ω × ℝ => X z.2 z.1) := by
    funext z
    rfl
  refine ⟨?_,?_,?_⟩
  · rw [he]
    exact hr.2.1.indicator (measurableSet_Ioc.preimage measurable_snd)
  · intro b hb
    letI : MeasurableSpace (Ω × Icc (0:ℝ) b) :=
      progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))
    have hm : Measurable (fun z : Ω × Icc (0:ℝ) b => X z.2.val z.1) :=
      continuous_adapted_real_progressive B.F B.mono (fun z => X z.2 z.1) b hb
        (fun r h => hr.2.2 r h.1) (fun w => (hr.1 w).continuousOn)
    have ht : Measurable (fun z : Ω × Icc (0:ℝ) b => z.2.val) :=
      continuous_adapted_real_progressive B.F B.mono (fun z : Ω × ℝ => z.2) b hb
        (fun _ _ => measurable_const) (fun _ => continuous_id.continuousOn)
    exact hm.indicator (measurableSet_Ioc.preimage ht)
  · intro b hb w
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
    have hi : IntegrableOn (fun r => (X r w)^2) (Ioc 0 b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp (((hr.1 w).pow 2).intervalIntegrable 0 b)
    have hie := hi.indicator (measurableSet_Ioc : MeasurableSet (Ioc s e))
    convert hie using 1
    funext r
    by_cases h : r ∈ Ioc s e <;> simp [brownianCellIntegrand,X,h]

end Asakura.Chapter7
