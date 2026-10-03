import Chapter12CompactIntegrandRestriction

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- A bounded-interval step pairing computed on the half-line is the same
pairing on the compact time type used for the Malliavin derivative. -/
theorem compact_step_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0 ≤ T)
    (a b : Icc (0:ℝ) T) (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (G : Ω → ℝ) (hG : Measurable G) :
    (∫ z,H z*(Ioc a.val b.val).indicator (fun _ => G z.1) z.2
      ∂P.prod (volume.restrict (Ioi (0:ℝ)))) =
      ∫ z : Ω × Icc (0:ℝ) T,H (z.1,z.2.val)*(Ico a b).indicator (fun _ => G z.1) z.2
        ∂P.prod (compactTimeMeasure T hT) := by
  let K : Ω × ℝ → ℝ := fun z => H z*(Ioc a.val b.val).indicator (fun _ => G z.1) z.2
  have hK : Measurable K := hH.mul ((hG.comp measurable_fst).indicator
    (measurableSet_Ioc.preimage measurable_snd))
  have hsupport : (∫ z,K z ∂P.prod (volume.restrict (Ioi (0:ℝ)))) =
      ∫ z,K z ∂P.prod ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) := by
    nth_rw 2 [← (Measure.restrict_univ (μ := P))]
    rw [Measure.prod_restrict]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have ht : z.2 ∉ Ioc a.val b.val := by
      intro hh
      exact hz ⟨mem_univ _,hh.2.trans b.property.2⟩
    simp [K,ht]
  have hmp := (MeasurePreserving.id P).prod (compact_time_val_preserving T hT)
  have hmap := integral_map (μ := P.prod (compactTimeMeasure T hT)) hmp.measurable.aemeasurable hK.aestronglyMeasurable
  rw [hmp.map_eq] at hmap
  calc
    _ = ∫ z,K z ∂P.prod ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) := hsupport
    _ = ∫ z : Ω × Icc (0:ℝ) T,K (z.1,z.2.val) ∂P.prod (compactTimeMeasure T hT) := hmap
    _ = _ := by
      apply integral_congr_ae
      have he : (Ico a b : Set (Icc (0:ℝ) T)) =ᵐ[compactTimeMeasure T hT] Ioc a b := Ico_ae_eq_Ioc
      have heprod := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := compactTimeMeasure T hT)).ae he
      filter_upwards [heprod] with z hz
      have hh : z.2.val ∈ Ioc a.val b.val ↔ z.2 ∈ Ico a b := Iff.of_eq hz.symm
      by_cases ht : z.2 ∈ Ico a b <;> simp [K,ht,hh]

end Asakura.Chapter12
