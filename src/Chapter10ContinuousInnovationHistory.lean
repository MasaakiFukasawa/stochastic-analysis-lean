import Chapter10PathInformation

open MeasureTheory Set
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The continuous prefix path and the collection of all its coordinate
values generate exactly the same information. This connects the two concrete
history representations used by the reconstruction and Gaussian arguments. -/
theorem continuous_innovation_history {Ω : Type*} {d r : ℕ} (T : ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (κ : Fin r → Fin d)
    (t : Icc (0:ℝ) T)
    (I : Ω → C(Icc (0:ℝ) t.val,Fin r → ℝ))
    (hI : ∀ w (s : Icc (0:ℝ) t.val) j,I w s j=X w ⟨s.val,s.property.1,s.property.2.trans t.property.2⟩ (κ j)) :
    MeasurableSpace.comap I inferInstance=pathInformation T X κ t := by
  apply le_antisymm
  · letI : MeasurableSpace Ω := pathInformation T X κ t
    apply Measurable.comap_le
    apply ContinuousMap.measurable_iff_eval.mpr
    intro s
    apply Measurable.of_eval
    intro j
    have hh := (measurable_pi_apply
      ((⟨⟨s.val,s.property.1,s.property.2.trans t.property.2⟩,s.property.2⟩ :
        {u : Icc (0:ℝ) T // u.val≤t.val}),j)).comp
      (show Measurable (fun w (z : {u : Icc (0:ℝ) T // u.val≤t.val} × Fin r) =>
        X w z.1.val (κ z.2)) from Measurable.of_comap_le le_rfl)
    simpa only [Function.comp_def,←hI] using hh
  · letI : MeasurableSpace Ω := MeasurableSpace.comap I inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro z
    let s : Icc (0:ℝ) t.val := ⟨z.1.val.val,z.1.val.property.1,z.1.property⟩
    have hh := (measurable_pi_apply z.2).comp ((continuous_eval_const s).measurable.comp
      (show Measurable I from Measurable.of_comap_le le_rfl))
    simpa only [Function.comp_def,hI,s] using hh

end Asakura.Chapter10
