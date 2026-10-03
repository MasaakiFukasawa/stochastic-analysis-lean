import EndToEndFiniteParameterExtension

open MeasureTheory Set Filter
open scoped Classical
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A common exceptional event for all parameters and finite time intervals
 can be removed without losing progressive measurability. -/
theorem parameter_coefficient_null_repair {Ω E : Type} {m : MeasurableSpace Ω}
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (B : BrownianSystem P d)
    (H : E × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b, 0 < b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ᵐ w ∂P, ∀ b, 0 ≤ b → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x r, r ∈ Icc 0 b → |H (x,(w,r))| ≤ K) :
    ∃ G : E × (Ω × ℝ) → ℝ, Measurable G ∧
    (∀ b, 0 < b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => G (z.1,(z.2.1,z.2.2.val)))) ∧
    (∀ w b, 0 ≤ b → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x r, r ∈ Icc 0 b → |G (x,(w,r))| ≤ K) ∧
    (∀ᵐ w ∂P, ∀ x r, G (x,(w,r)) = H (x,(w,r))) := by
  let Bad := {w | ¬ ∀ b, 0 ≤ b → ∃ K : ℝ, 0 ≤ K ∧
    ∀ x r, r ∈ Icc 0 b → |H (x,(w,r))| ≤ K}
  let N := toMeasurable P Bad
  have hNm : MeasurableSet N := measurableSet_toMeasurable P Bad
  have hN0 : P N = 0 := (measure_toMeasurable (μ:=P) Bad).trans (ae_iff.mp hb)
  let G := fun z : E × (Ω × ℝ) => if z.2.1 ∈ N then 0 else H z
  have hGp b (hb : 0 < b) : @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => G (z.1,(z.2.1,z.2.2.val))) := by
    have hset : @MeasurableSet (Ω × Icc (0:ℝ) b)
        (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))
        {z | z.1 ∈ N} := by
      apply MeasurableSpace.measurableSet_iInf.mpr
      intro t
      exact (B.null (realTimeClamp t.val) N hNm hN0).preimage measurable_fst
    exact measurable_const.ite (hset.preimage measurable_snd) (hp b hb)
  refine ⟨G,measurable_const.ite (hNm.preimage (measurable_fst.comp measurable_snd)) hm,hGp,?_,?_⟩
  · intro w b hb
    by_cases hw : w ∈ N
    · refine ⟨0,le_rfl,?_⟩
      intro x r hr
      simp only [G,if_pos hw,abs_zero,le_refl]
    · have hgood : w ∉ Bad := fun hn => hw (subset_toMeasurable P Bad hn)
      have hbound : ∀ b, 0 ≤ b → ∃ K : ℝ, 0 ≤ K ∧
          ∀ x r, r ∈ Icc 0 b → |H (x,(w,r))| ≤ K := by simpa only [Bad,mem_setOf_eq,not_not] using hgood
      obtain ⟨K,hK,hbound⟩ := hbound b hb
      exact ⟨K,hK,fun x r hr => by simpa only [G,if_neg hw] using hbound x r hr⟩
  · have hae : ∀ᵐ w ∂P, w ∉ N := by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hN0
    filter_upwards [hae] with w hw
    intro x r
    simp only [G,if_neg hw]

#print axioms parameter_coefficient_null_repair
end Asakura.EndToEnd
