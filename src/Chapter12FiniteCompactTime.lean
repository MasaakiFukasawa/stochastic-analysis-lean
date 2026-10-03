import Chapter12CompactTimeMeasure
import Chapter12FiniteWienerIndicator

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem finite_time_measure_eq (T : ℝ) :
    (volume.restrict (Ioi (0:ℝ))).restrict (Iic T) = volume.restrict (Ioc 0 T) := by
  rw [Measure.restrict_restrict measurableSet_Iic]
  congr 1
  ext t
  simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]
  exact and_comm

theorem compact_time_val_preserving (T : ℝ) (hT : 0 ≤ T) :
    MeasurePreserving (Subtype.val : Icc (0:ℝ) T → ℝ) (compactTimeMeasure T hT)
      ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) := by
  refine ⟨measurable_subtype_coe,?_⟩
  rw [finite_time_measure_eq]
  unfold compactTimeMeasure
  rw [Measure.map_map measurable_subtype_coe
    (continuous_projIcc (a := 0) (b := T) (h := hT)).measurable]
  calc
    _ = Measure.map id (volume.restrict (Ioc (0:ℝ) T)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact congrArg Subtype.val (projIcc_of_mem hT ⟨ht.1.le,ht.2⟩)
    _ = _ := Measure.map_id

theorem compact_time_proj_preserving (T : ℝ) (hT : 0 ≤ T) :
    MeasurePreserving (projIcc 0 T hT) ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))
      (compactTimeMeasure T hT) := by
  refine ⟨(continuous_projIcc (a := 0) (b := T) (h := hT)).measurable,?_⟩
  rw [finite_time_measure_eq]
  rfl

noncomputable def finiteTimeToCompact (T : ℝ) (hT : 0 ≤ T) :
    Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) →ₗᵢ[ℝ]
      Lp ℝ 2 (compactTimeMeasure T hT) :=
  Lp.compMeasurePreservingₗᵢ ℝ Subtype.val (compact_time_val_preserving T hT)

noncomputable def compactTimeToFinite (T : ℝ) (hT : 0 ≤ T) :
    Lp ℝ 2 (compactTimeMeasure T hT) →ₗᵢ[ℝ]
      Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (projIcc 0 T hT) (compact_time_proj_preserving T hT)

instance compactTimeMeasure_nullSingleton (T : ℝ) (hT : 0 ≤ T) :
    NullSingletonClass (compactTimeMeasure T hT) := by
  constructor
  intro t
  have hh := (compact_time_val_preserving T hT).measure_preimage (measurableSet_singleton t.val).nullMeasurableSet
  have hp : (Subtype.val : Icc (0:ℝ) T → ℝ) ⁻¹' {t.val} = {t} := by
    ext s
    simp only [mem_preimage,mem_singleton_iff,Subtype.val_inj]
  rw [hp] at hh
  exact hh.trans (measure_singleton t.val)

theorem finite_time_compact_interval (T : ℝ) (hT : 0 ≤ T) (a b : Icc (0:ℝ) T) :
    (finiteTimeToCompact T hT (finiteTimeIntervalVector T a b) : Icc (0:ℝ) T → ℝ)
      =ᵐ[compactTimeMeasure T hT] (Ico a b).indicator (fun _ => (1:ℝ)) := by
  have hi : (finiteTimeIntervalVector T a b : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
      (Ioc a.val b.val).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hh := (compact_time_val_preserving T hT).quasiMeasurePreserving.ae_eq_comp hi
  have he : (Ico a b : Set (Icc (0:ℝ) T)) =ᵐ[compactTimeMeasure T hT] Ioc a b := Ico_ae_eq_Ioc
  filter_upwards [Lp.coeFn_compMeasurePreserving (finiteTimeIntervalVector T a b)
    (compact_time_val_preserving T hT),hh,he] with t ht hu heq
  change finiteTimeToCompact T hT (finiteTimeIntervalVector T a b) t = _
  change Lp.compMeasurePreserving Subtype.val (compact_time_val_preserving T hT)
    (finiteTimeIntervalVector T a b) t = _
  rw [ht,hu]
  change (Ioc a.val b.val).indicator (fun _ => (1:ℝ)) t.val = _
  have hm : t.val ∈ Ioc a.val b.val ↔ t ∈ Ico a b := Iff.of_eq heq.symm
  by_cases h : t ∈ Ico a b
  · simp [h,hm.mpr h]
  · simp [h,mt hm.mp h]

/-- Pairing with the deterministic interval direction is the ordinary
integral over that time interval, with the endpoint convention of chapter 2. -/
theorem finite_compact_interval_inner (T : ℝ) (hT : 0 ≤ T)
    (a b : Icc (0:ℝ) T)
    (f : Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) :
    inner ℝ f (finiteTimeIntervalVector T a b) =
      ∫ t in Ico a b, finiteTimeToCompact T hT f t ∂compactTimeMeasure T hT := by
  rw [← (finiteTimeToCompact T hT).inner_map_map f (finiteTimeIntervalVector T a b),L2.inner_def]
  rw [← integral_indicator measurableSet_Ico]
  apply integral_congr_ae
  filter_upwards [finite_time_compact_interval T hT a b] with t ht
  rw [ht]
  change (Ico a b).indicator (fun _ => (1:ℝ)) t * finiteTimeToCompact T hT f t = _
  by_cases h : t ∈ Ico a b <;> simp [h]

end Asakura.Chapter12
