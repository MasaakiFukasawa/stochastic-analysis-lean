import Chapter11FiniteIntegral

open MeasureTheory Set
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- A strategy given only on the book's finite interval admits a globally
 measurable progressive bounded extension. Thus the global formal interface
 does not strengthen the manuscript's admissibility class. -/
theorem finite_bounded_strategy_extension {Ω : Type*} [m : MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (R : ℝ) (hR : 0≤R) (π : Ω × Icc (0:ℝ) R → ℝ)
    (hp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance π)
    (K : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K) :
    ∃ H : Ω × ℝ → ℝ,Measurable H ∧ (∀ z,|H z|≤K) ∧
      (∀ d,0<d → @Measurable _ _
        (progressiveSpace (fun t : Icc (0:ℝ) d => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val))) ∧
      ∀ w (t : Icc (0:ℝ) R),H (w,t.val)=π (w,t) := by
  letI : Fact ((0:ℝ)≤R) := ⟨hR⟩
  have hm : Measurable π := hp.mono (progressive_space_le_product _ (fun t => hle (realTimeClamp t.val))) le_rfl
  let G := fun z : Ω × ℝ => π (z.1,projIcc 0 R hR z.2)
  have hG : Measurable G := hm.comp (measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd))
  have hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)) := by
    have he : (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val))=π := by
      funext z
      dsimp only [G]
      rw [projIcc_of_mem hR z.2.property]
    rw [he];exact hp
  let H := fun z : Ω × ℝ => (Iic R).indicator (fun s => G (z.1,s)) z.2
  have hHm : Measurable H := by
    change Measurable ((Prod.snd ⁻¹' Iic R).indicator G)
    exact hG.indicator (measurableSet_Iic.preimage measurable_snd)
  refine ⟨H,hHm,?_,?_,?_⟩
  · intro z
    by_cases hz : z.2∈Iic R
    · change |(Iic R).indicator (fun s => G (z.1,s)) z.2|≤K
      rw [indicator_of_mem hz]
      exact hb _
    · change |(Iic R).indicator (fun s => G (z.1,s)) z.2|≤K
      rw [indicator_of_notMem hz,abs_zero];exact hK
  · intro d _
    exact progressive_finite_zero_extension _ (hF.comp real_time_clamp_mono) R hR G hGp d
  · intro w t
    dsimp only [H,G]
    rw [indicator_of_mem (show t.val∈Iic R from t.property.2),projIcc_of_mem hR t.property]

end Asakura.Chapter11
