import Extended
open MeasureTheory Filter Set
open scoped Topology
namespace Asakura

/-- A.5.2, for real-valued functions: null-augmentation measurability admits
an everywhere real-valued G-measurable version. Rational cuts avoid infinite
values on the exceptional null set. -/
theorem nullAugmentation_real_version {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (G : MeasurableSpace Ω) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ (nullAugmentation (m := m) μ G) _ f) :
    ∃ g : Ω → ℝ, @Measurable Ω ℝ G _ g ∧ f =ᵐ[μ] g := by
  classical
  have hcuts : ∀ q : ℚ, ∃ B : Set Ω, MeasurableSet[G] B ∧
      {x | f x < (q : ℝ)} =ᵐ[μ] B := by
    intro q
    exact (hf measurableSet_Iio).2
  choose B hBm hBeq using hcuts
  let F : Ω → EReal := fun x => ⨅ q : ℚ, if x ∈ B q then ((q : ℝ) : EReal) else ⊤
  have hFm : @Measurable Ω EReal G _ F := by
    apply Measurable.iInf
    intro q
    exact Measurable.ite (hBm q) measurable_const measurable_const
  have hFeq : (fun x => (f x : EReal)) =ᵐ[μ] F := by
    have hgood : ∀ᵐ x ∂μ, ∀ q : ℚ, (f x < (q : ℝ)) = (x ∈ B q) :=
      (ae_all_iff).2 (fun q => hBeq q)
    filter_upwards [hgood] with x hx
    apply le_antisymm
    · apply le_iInf
      intro q
      split_ifs with hq
      · exact EReal.coe_le_coe_iff.mpr ((iff_of_eq (hx q)).mpr hq).le
      · exact le_top
    · by_contra h
      have hlt : (f x : EReal) < F x := lt_of_not_ge h
      obtain ⟨y, hyf, hyF⟩ := EReal.exists_between_coe_real hlt
      obtain ⟨q, hqf, hqy⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp hyf)
      have hqB : x ∈ B q := (iff_of_eq (hx q)).mp hqf
      have hFq : F x ≤ ((q : ℝ) : EReal) := by
        exact (iInf_le (fun q : ℚ => if x ∈ B q then ((q : ℝ) : EReal) else ⊤) q).trans
          (by simp [hqB])
      exact (not_lt_of_ge hFq) ((EReal.coe_lt_coe_iff.mpr hqy).trans hyF)
  refine ⟨fun x => (F x).toReal, measurable_ereal_toReal.comp hFm, ?_⟩
  filter_upwards [hFeq] with x hx
  simpa using congrArg EReal.toReal hx
end Asakura
