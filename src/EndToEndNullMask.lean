import EndToEndHJMGlobalRandom
import Chapter7ItoCommonIntegrand

open MeasureTheory Set Filter
open scoped Classical
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Null-event repair preserves the actual continuous local martingale. -/
theorem local_martingale_null_mask {Ω : Type} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (E:Set Ω) (hE:MeasurableSet E) (hE0:P E=0)
    (X:HalfClosedTime → Ω → ℝ) (hX:LocalMProcessWitness P B.F X) :
    LocalMProcessWitness P B.F (fun t w => if w∈E then 0 else X t w) := by
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P B.F B.mono hX
  · intro t ht
    exact measurable_const.ite (B.null t E hE hE0) (hX.adapted P B.F t ht)
  · intro w t ht
    by_cases hw:w∈E
    · simpa only [if_pos hw] using (continuousAt_const : ContinuousAt (fun _ : HalfClosedTime => (0:ℝ)) t)
    · simpa only [if_neg hw] using hX.path P B.F w t ht
  · have hae : ∀ᵐw∂P,w∉E := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hE0
    filter_upwards [hae] with w hw
    exact fun _ _ => by simp only [if_neg hw]

/-- The same common null mask can be applied to an Ito integrand and integral. -/
theorem ito_null_mask {Ω : Type} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (E:Set Ω) (hE:MeasurableSet E) (hE0:P E=0) (i:Fin d)
    (H:Ω × ℝ → ℝ) (X:HalfClosedTime → Ω → ℝ)
    (hX:LocalMProcessWitness P B.F X) (hI:ItoCovarianceFormula P B.F (B.W i) H X) :
    ItoCovarianceFormula P B.F (B.W i) (fun z => if z.1∈E then 0 else H z)
      (fun t w => if w∈E then 0 else X t w) := by
  have hae : ∀ᵐw∂P,w∉E := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hE0
  have hi := Asakura.Chapter7.ito_integrand_common_ae P B.F (B.W i) X H
    (fun z => if z.1∈E then 0 else H z) hI (by
      filter_upwards [hae] with w hw
      exact fun _ => by simp only [if_neg hw])
  apply ItoCovarianceFormula.congr_integral P B.F B.mono B.le (B.W i) X _ _ hX
    (local_martingale_null_mask P B E hE hE0 X hX) _ hi
  filter_upwards [hae] with w hw
  exact fun _ _ => by simp only [if_neg hw]

/-- A null event is measurable at every time, so masking also preserves
joint parameter/progressive measurability. -/
theorem coefficient_null_mask {Ω : Type} [MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (E:Set Ω) (hE:MeasurableSet E) (hE0:P E=0)
    (H:ℝ × (Ω × ℝ) → ℝ) (hm:Measurable H)
    (hp:∀b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z:ℝ × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val)))) :
    let G := fun z:ℝ × (Ω × ℝ) => if z.2.1∈E then 0 else H z
    Measurable G ∧
      ∀b,0<b → @Measurable _ _
        ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
        (fun z:ℝ × (Ω × Icc (0:ℝ) b) => G (z.1,(z.2.1,z.2.2.val))) := by
  refine ⟨measurable_const.ite (hE.preimage (measurable_fst.comp measurable_snd)) hm,?_⟩
  intro b hb
  have he : @MeasurableSet (Ω × Icc (0:ℝ) b)
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) {z | z.1∈E} := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro t
    exact (B.null (realTimeClamp t.val) E hE hE0).preimage measurable_fst
  exact measurable_const.ite (he.preimage measurable_snd) (hp b hb)

#print axioms local_martingale_null_mask
#print axioms ito_null_mask
#print axioms coefficient_null_mask
end Asakura.EndToEnd
