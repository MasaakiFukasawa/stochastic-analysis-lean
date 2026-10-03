import Chapter5ProgressiveDriftVariation
import Chapter2LocalIntegrableRepresentative

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Completion removes one sample-null set. The finite-energy driver has
an everywhere integrable progressive representative, with equality at
all times outside that same null set. -/
theorem finite_energy_drift_representative
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (R : ℝ) (hR : 0≤R) (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hG2 : MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    ∃ J : Ω × ℝ → ℝ,Measurable J ∧
      (@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) R => J (z.1,z.2.val))) ∧
      (∀ w,Integrable (fun r => J (w,r)) (volume.restrict (Ioc 0 R))) ∧
      (∀ᵐ w ∂P,∀ r,J (w,r)=G (w,r)) := by
  have hi : ∀ᵐ w ∂P,Integrable (fun r => G (w,r)) (volume.restrict (Ioc 0 R)) :=
    (finite_time_L2_sections P R hR G hGm hG2).1.mono (fun w hw => hw.integrable (by norm_num))
  let bad := {w | ¬ Integrable (fun r => G (w,r)) (volume.restrict (Ioc 0 R))}
  let N := toMeasurable P bad
  have hNz : P N=0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hi
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  let J := fun z : Ω × ℝ => if z.1∈N then 0 else G z
  refine ⟨J,Measurable.ite (hNm.preimage measurable_fst) measurable_const hGm,?_,?_,?_⟩
  · apply (measurable_progressive_iff _ _).mpr
    intro t
    exact Measurable.ite ((hnull _ N hNm hNz).preimage measurable_fst) measurable_const
      ((measurable_progressive_iff _ _).mp hGp t)
  · intro w
    by_cases hw : w∈N
    · simp only [J,if_pos hw]
      refine ⟨aestronglyMeasurable_const,?_⟩
      simp [hasFiniteIntegral_iff_norm]
    · have hiw : Integrable (fun r => G (w,r)) (volume.restrict (Ioc 0 R)) := by
        by_contra hh
        exact hw (subset_toMeasurable P bad hh)
      simpa only [J,if_neg hw] using hiw
  · have hn : ∀ᵐ w ∂P,w∉N := by
      rw [ae_iff]
      simpa only [not_not,setOf_mem_eq] using hNz
    exact hn.mono (fun w hw r => if_neg hw)

end Asakura.Chapter5
