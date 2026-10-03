import Chapter2CoordinateMetricEquivalence
import Chapter2TimeExhaustion

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {T : EReal} [Fact (0 ≤ T)]

theorem finite_time_segment_compact (v : ClosedTime T) (hv : v < ⊤) :
    IsCompact {s : Iio (⊤ : ClosedTime T) | s.val ≤ v} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : Subtype.val '' {s : Iio (⊤ : ClosedTime T) | s.val ≤ v} = Iic v := by
    ext s
    constructor
    · rintro ⟨s,hs,rfl⟩; exact hs
    · intro hs; exact ⟨⟨s,hs.trans_lt hv⟩,hs,rfl⟩
  rw [he]
  exact isClosed_Iic.isCompact

noncomputable def finiteTimeStageDist (v : ClosedTime T) (hv : v < ⊤)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) : ℝ := by
  letI : CompactSpace {s : Iio (⊤ : ClosedTime T) | s.val ≤ v} :=
    isCompact_iff_compactSpace.mp (finite_time_segment_compact v hv)
  exact dist (f.restrict {s | s.val ≤ v}) (g.restrict {s | s.val ≤ v})

theorem finite_time_stage_nonneg (v : ClosedTime T) (hv : v < ⊤)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) : 0 ≤ finiteTimeStageDist v hv f g := by
  letI : CompactSpace {s : Iio (⊤ : ClosedTime T) | s.val ≤ v} :=
    isCompact_iff_compactSpace.mp (finite_time_segment_compact v hv)
  unfold finiteTimeStageDist
  exact dist_nonneg

theorem finite_time_stage_measurable {Ω : Type*} [MeasurableSpace Ω]
    (v : ClosedTime T) (hv : v < ⊤)
    (X Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ)) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => finiteTimeStageDist v hv (X ω) (Y ω)) := by
  letI : CompactSpace {s : Iio (⊤ : ClosedTime T) | s.val ≤ v} :=
    isCompact_iff_compactSpace.mp (finite_time_segment_compact v hv)
  have hx : Measurable (fun ω => (X ω).restrict {s | s.val ≤ v}) :=
    ContinuousMap.measurable_iff_eval.mpr (fun s => (ContinuousMap.measurable_eval s.val).comp hX)
  have hy : Measurable (fun ω => (Y ω).restrict {s | s.val ≤ v}) :=
    ContinuousMap.measurable_iff_eval.mpr (fun s => (ContinuousMap.measurable_eval s.val).comp hY)
  exact hx.dist hy

theorem finite_time_stage_mono (v w : ClosedTime T) (hv : v < ⊤) (hw : w < ⊤) (hvw : v ≤ w)
    (f g : C(Iio (⊤ : ClosedTime T),ℝ)) :
    finiteTimeStageDist v hv f g ≤ finiteTimeStageDist w hw f g := by
  letI : CompactSpace {s : Iio (⊤ : ClosedTime T) | s.val ≤ v} :=
    isCompact_iff_compactSpace.mp (finite_time_segment_compact v hv)
  letI : CompactSpace {s : Iio (⊤ : ClosedTime T) | s.val ≤ w} :=
    isCompact_iff_compactSpace.mp (finite_time_segment_compact w hw)
  unfold finiteTimeStageDist
  rw [dist_eq_norm,dist_eq_norm]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro s
  exact ContinuousMap.norm_coe_le_norm
    (f.restrict {s | s.val ≤ w}-g.restrict {s | s.val ≤ w}) ⟨s.val,s.property.trans hvw⟩

/-- The manuscript explicitly allows nonmonotone horizon sequences. Their
actual supremum norms give the same expected-metric convergence for any two
cofinal sequences; no monotonicity assumption is introduced. -/
theorem arbitrary_time_metric_equivalence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u v : ℕ → ClosedTime T) (hu : ∀ n, u n < ⊤) (hv : ∀ n, v n < ⊤)
    (huc : ⨆ n, u n = ⊤) (hvc : ⨆ n, v n = ⊤)
    (X Y : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) :
    Tendsto (fun n => ∫ ω, coordinateMetric (fun j => fun ω => finiteTimeStageDist (u j) (hu j) (X n ω) (Y n ω)) ω ∂P) atTop (𝓝 0) ↔
    Tendsto (fun n => ∫ ω, coordinateMetric (fun j => fun ω => finiteTimeStageDist (v j) (hv j) (X n ω) (Y n ω)) ω ∂P) atTop (𝓝 0) := by
  apply coordinate_metric_cofinal_equivalence P _ _
    (fun n j => finite_time_stage_measurable (u j) (hu j) (X n) (Y n) (hX n) (hY n))
    (fun n j => finite_time_stage_measurable (v j) (hv j) (X n) (Y n) (hX n) (hY n))
    (fun n j ω => finite_time_stage_nonneg (u j) (hu j) (X n ω) (Y n ω))
    (fun n j ω => finite_time_stage_nonneg (v j) (hv j) (X n ω) (Y n ω))
  · intro j
    have hlt : u j < ⨆ n, v n := hvc ▸ hu j
    obtain ⟨k,hk⟩ := lt_iSup_iff.mp hlt
    exact ⟨k,fun n ω => finite_time_stage_mono _ _ (hu j) (hv k) hk.le _ _⟩
  · intro j
    have hlt : v j < ⨆ n, u n := huc ▸ hv j
    obtain ⟨k,hk⟩ := lt_iSup_iff.mp hlt
    exact ⟨k,fun n ω => finite_time_stage_mono _ _ (hv j) (hu k) hk.le _ _⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.arbitrary_time_metric_equivalence
