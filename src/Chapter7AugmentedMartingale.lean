import Chapter7ProductMartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma sigma_le_null_augmentation
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) (G : MeasurableSpace Ω) (hle : G ≤ m) :
    G ≤ Asakura.nullAugmentation (m := m) P G := fun E hE => ⟨hle E hE,E,hE,.rfl⟩

lemma null_augmentation_null
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) (G : MeasurableSpace Ω)
    (N : Set Ω) (hm : MeasurableSet[m] N) (hz : P N = 0) :
    MeasurableSet[Asakura.nullAugmentation (m := m) P G] N := by
  refine ⟨hm,∅,MeasurableSet.empty,ae_eq_set.mpr ?_⟩
  simpa using And.intro hz (measure_empty (μ := P))

/-- Null augmentation leaves the actual M2 martingale identity unchanged. -/
theorem m2_null_augmentation
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) :
    ContinuousM2Witness P (fun t => Asakura.nullAugmentation (m := m) P (F t)) X := by
  refine ⟨fun t => (hX.adapted t).mono (sigma_le_null_augmentation P (F t) (hle t)) le_rfl,
    hX.moment,hX.path,?_,hX.initial⟩
  intro s t hst
  exact (conditional_null_augmentation P (F s) (hle s) (X t)
    ((hX.moment t).integrable (by norm_num))).symm.trans (hX.martingale s t hst)

theorem local_null_augmentation
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    LocalMProcessWitness P (fun t => Asakura.nullAugmentation (m := m) P (F t)) X := by
  obtain ⟨τ,hs,hm,ht,hc,hb⟩ := hX.localizers
  exact ⟨τ,fun j t => sigma_le_null_augmentation P (F t) (hle t) _ (hs j t),hm,ht,hc,
    fun j => ⟨m2_null_augmentation P F hle _ (hb j).1,(hb j).2⟩⟩

theorem variation_null_augmentation
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (A : ClosedTime T → Ω → ℝ) (hA : LocalVariationWitness F A) :
    LocalVariationWitness (fun t => Asakura.nullAugmentation (m := m) P (F t)) A := by
  obtain ⟨τ,hs,hm,ht,hc,hb⟩ := hA.localizers
  exact ⟨τ,fun j t => sigma_le_null_augmentation P (F t) (hle t) _ (hs j t),hm,ht,hc,hb⟩

theorem covariance_null_augmentation
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (X Y A : ClosedTime T → Ω → ℝ) (hA : LocalCovarianceWitness P F X Y A) :
    LocalCovarianceWitness P (fun t => Asakura.nullAugmentation (m := m) P (F t)) X Y A :=
  ⟨local_null_augmentation P F hle _ hA.defect,variation_null_augmentation P F hle A hA.variation⟩

end Asakura.Chapter7
