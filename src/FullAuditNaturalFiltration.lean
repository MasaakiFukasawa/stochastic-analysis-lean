import FullAuditConditionalLimit
import Extended
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The unaugmented natural sigma algebra at time s, with all past times. -/
def pastSigma {Ω ι : Type*} [Preorder ι] (X : ι → Ω → ℝ) (s : ι) : MeasurableSpace Ω :=
  ⨆ t : Iic s, (borel ℝ).comap (X t.val)

theorem past_sigma_le {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[m] (X t)) (s : ι) : pastSigma X s ≤ m :=
  iSup_le fun t => (hm t.val).comap_le

theorem past_sigma_mono {Ω ι : Type*} [Preorder ι] (X : ι → Ω → ℝ) : Monotone (pastSigma X) := by
  intro s t hst
  apply iSup_le
  intro r
  exact le_iSup_of_le (⟨r.val,r.property.trans hst⟩ : Iic t) le_rfl

theorem natural_process_adapted {Ω ι : Type*} [Preorder ι] (X : ι → Ω → ℝ) (s : ι) :
    Measurable[pastSigma X s] (X s) := by
  apply Measurable.of_comap_le
  exact le_iSup (fun t : Iic s => (borel ℝ).comap (X t.val)) ⟨s,le_rfl⟩

theorem past_sigma_history {Ω ι : Type*} [Preorder ι] (X : ι → Ω → ℝ) (s : ι) :
    pastSigma X s = MeasurableSpace.comap (fun ω (t : Iic s) => X t.val ω) inferInstance := by
  simp only [pastSigma,MeasurableSpace.pi,MeasurableSpace.comap_iSup,MeasurableSpace.comap_comp,Function.comp_def,BorelSpace.measurable_eq]

/-- The exact null augmentation in the manuscript does not change conditional
 expectations: use the measurable set representative and C2. -/
theorem conditional_null_augmentation {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G ≤ m)
    (Y : Ω → ℝ) (hY : Integrable Y P) :
    P[Y | G] =ᵐ[P] P[Y | Asakura.nullAugmentation (m := m) P G] := by
  letI : MeasurableSpace Ω := m
  let H := Asakura.nullAugmentation (m := m) P G
  letI : MeasurableSpace Ω := m
  have hHm : H ≤ m := fun A hA => hA.1
  have hGH : G ≤ H := fun A hA => ⟨hG A hA,A,hA,EventuallyEq.rfl⟩
  apply ae_eq_condExp_of_forall_setIntegral_eq hHm hY
    (fun _ _ _ => integrable_condExp.integrableOn) _
    ((stronglyMeasurable_condExp (μ := P) (m := G) (f := Y)).mono hGH).aestronglyMeasurable
  intro A hA hfin
  obtain ⟨hAm,B,hB,hAB⟩ := hA
  rw [setIntegral_congr_set hAB,setIntegral_condExp hG hY hB,setIntegral_congr_set hAB.symm]

/-- Augmentation preserves the ordering of a filtration. -/
theorem null_augmentation_mono {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) {G H : MeasurableSpace Ω} (hGH : G ≤ H) :
    Asakura.nullAugmentation (m := m) P G ≤ Asakura.nullAugmentation (m := m) P H := by
  rintro A ⟨hAm,B,hB,hAB⟩
  exact ⟨hAm,B,hGH _ hB,hAB⟩

/-- An adapted natural-filtration process stays adapted after augmentation. -/
theorem natural_augmented_adapted {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hm : ∀ t, Measurable[m] (X t)) (s : ι) :
    Measurable[Asakura.nullAugmentation (m := m) P (pastSigma X s)] (X s) := by
  apply (natural_process_adapted X s).mono _ le_rfl
  intro A hA
  exact ⟨past_sigma_le X hm s A hA,A,hA,EventuallyEq.rfl⟩

end Asakura.FullAudit
