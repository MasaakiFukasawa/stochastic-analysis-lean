import FullAuditNaturalFiltration
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false

/-- The book adds ambient measurable null sets, not every subset of them.
That exact assumption suffices for an ambient measurable modification. -/
theorem measurable_modification_of_null_sets
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (G : MeasurableSpace Ω) (hle : G ≤ m)
    (hnull : ∀ N, MeasurableSet[m] N → P N = 0 → MeasurableSet[G] N)
    (f g : Ω → ℝ) (hf : Measurable[G] f) (hg : Measurable[m] g)
    (he : f =ᵐ[P] g) : Measurable[G] g := by
  let N := {ω | f ω ≠ g ω}
  have hNm : MeasurableSet[m] N := (measurableSet_eq_fun (hf.mono hle le_rfl) hg).compl
  have hN0 : P N = 0 := by
    exact ae_iff.mp he
  have hNG := hnull N hNm hN0
  intro s hs
  have hsn : MeasurableSet[G] (g ⁻¹' s ∩ N) :=
    hnull _ ((hg hs).inter hNm) (measure_mono_null inter_subset_right hN0)
  have hid : g ⁻¹' s = (f ⁻¹' s \ N) ∪ (g ⁻¹' s ∩ N) := by
    ext ω
    by_cases h : f ω = g ω <;> simp [N,h]
  rw [hid]
  exact ((hf hs).diff hNG).union hsn

/-- The common equality event of continuous processes is measurable,
not merely an outer-measure-one statement. -/
theorem continuous_equality_event_measurable
    {Ω D : Type*} [MeasurableSpace Ω] [TopologicalSpace D]
    (S : Set D) (hc : S.Countable) (hd : Dense S)
    (X Y : D → Ω → ℝ) (hXm : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t))
    (hX : ∀ ω, Continuous (fun t => X t ω))
    (hY : ∀ ω, Continuous (fun t => Y t ω)) :
    MeasurableSet {ω | ∀ t, X t ω = Y t ω} := by
  letI : Countable S := hc.to_subtype
  have he : {ω | ∀ t, X t ω = Y t ω} = ⋂ t : S, {ω | X t ω = Y t ω} := by
    ext ω
    simp only [mem_setOf_eq,mem_iInter]
    constructor
    · intro h t
      exact h t
    · intro h t
      exact congrFun (Continuous.ext_on hd (hX ω) (hY ω) (fun t ht => h ⟨t,ht⟩)) t
  rw [he]
  exact MeasurableSet.iInter (fun t => measurableSet_eq_fun (hXm t) (hYm t))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.measurable_modification_of_null_sets
#print axioms Asakura.Chapter2Complete.continuous_equality_event_measurable
