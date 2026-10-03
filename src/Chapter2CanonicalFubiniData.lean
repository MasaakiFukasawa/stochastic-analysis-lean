import Chapter2CovarianceStieltjes
import Chapter2CovarianceContinuity
import Chapter2RandomStieltjes
import Chapter2WeightedPaths
import Chapter2RandomSignedVariation
import Chapter2CovarianceAbsoluteContinuity
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the signed measure used by the general covariance formula,
with its interval identities and interval CS bound on the original
quadratic-variation measures. -/
theorem canonical_covariance_measure_fubini_data
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hAm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 d))
    (hBm : ∀ ω, MonotoneOn (fun r => B (realTimeClamp r) ω) (Icc 0 d))
    (hAc : ∀ ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 d))
    (hBc : ∀ ω, ContinuousOn (fun r => B (realTimeClamp r) ω) (Icc 0 d)) :
    let α := fun ω => (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAm ω)
      (fun r hr => (hAc ω r hr).mono inter_subset_left)).measure
    let β := fun ω => (intervalStieltjes 0 d hd (fun r => B (realTimeClamp r) ω) (hBm ω)
      (fun r hr => (hBc ω r hr).mono inter_subset_left)).measure
    ∃ ν : Ω → SignedMeasure ℝ,
      (∀ᵐ ω ∂P, ∀ a b, a ≤ b → |ν ω (Ioc a b)| ≤
        Real.sqrt ((α ω).real (Ioc a b))*Real.sqrt ((β ω).real (Ioc a b))) ∧
      (∀ ω a b, 0 ≤ a → a ≤ b → ν ω (Ioc a b) =
        C (min (realTimeClamp b) (realTimeClamp d)) ω-C (min (realTimeClamp a) (realTimeClamp d)) ω) ∧
      Measurable (fun ω => (β ω).real univ) ∧
      Measurable (fun ω => (ν ω).totalVariation) ∧
      (∀ s t, Measurable (fun ω => ν ω (Ioc s t))) ∧
      (∀ᵐ ω ∂P, (ν ω).totalVariation (Iic 0) = 0) := by
  intro α β
  have hbelow r (hr : r ∈ Icc 0 d) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hdT
  let Cv := fun ω r => C (realTimeClamp r) ω
  have hCc ω : ContinuousOn (Cv ω) (Icc 0 d) := by
    intro r hr
    exact ((local_covariance_path_continuous P F X Y C hX hY hC ω _ (hbelow r hr)).comp
      real_time_clamp_continuous.continuousAt).continuousWithinAt
  let hrC := fun ω r (hr : r ∈ Icc 0 d) => (hCc ω r hr).mono (inter_subset_left (t := Ici r))
  let ν := fun ω => bvSigned (Cv ω ∘ intervalClamp 0 d hd)
    (intervalClamp_boundedVariation 0 d hd (Cv ω) (hC.variation.finite_boundedVariation F ω d hd hdT))
    (intervalClamp_right_continuous 0 d hd (Cv ω) (hrC ω)) 0
  have hcs : ∀ᵐ ω ∂P, ∀ a b, a ≤ b → |ν ω (Ioc a b)| ≤
      Real.sqrt ((α ω).real (Ioc a b))*Real.sqrt ((β ω).real (Ioc a b)) := by
    filter_upwards [local_covariance_interval_cs P F hF hle hnull X Y A B C hX hY hA hB hC] with ω hω
    intro a b hab
    rw [bvSigned_Ioc,intervalStieltjes_Ioc_real,intervalStieltjes_Ioc_real]
    · exact hω _ _ (real_time_clamp_mono (intervalClamp_mono 0 d hd hab))
        (hbelow _ (intervalClamp_mem 0 d hd b))
    all_goals exact hab
  refine ⟨ν,hcs,?_,?_,?_,?_,?_⟩
  · intro ω a b ha hab
    have hclamp r (hr : 0 ≤ r) : intervalClamp 0 d hd r = min r d := by
      by_cases hrd : r ≤ d
      · rw [intervalClamp_eq 0 d hd ⟨hr,hrd⟩,min_eq_left hrd]
      · simp only [intervalClamp,projIcc_of_right_le hd (le_of_not_ge hrd),min_eq_right (le_of_not_ge hrd)]
    rw [bvSigned_Ioc _ _ _ _ a b hab]
    dsimp only [Function.comp_def,Cv]
    rw [hclamp b (ha.trans hab),hclamp a ha,real_time_clamp_mono.map_min,real_time_clamp_mono.map_min]
  · have he : (fun ω => (β ω).real univ) = fun ω => B (realTimeClamp d) ω-B (realTimeClamp 0) ω := by
      funext ω
      rw [Measure.real,interval_stieltjes_total_mass 0 d hd (fun ω r => B (realTimeClamp r) ω) hBm
        (fun ω r hr => (hBc ω r hr).mono inter_subset_left)]
      exact ENNReal.toReal_ofReal (sub_nonneg.2 (hBm ω (left_mem_Icc.2 hd) (right_mem_Icc.2 hd) hd))
    rw [he]
    exact ((hB.adapted P F hY hY _ (hbelow d (right_mem_Icc.2 hd))).mono (hle _) le_rfl).sub
      ((hB.adapted P F hY hY _ (hbelow 0 (left_mem_Icc.2 hd))).mono (hle _) le_rfl)
  · have hclip ω : Continuous (Cv ω ∘ intervalClamp 0 d hd) :=
      (continuousOn_iff_continuous_restrict.mp (hCc ω)).comp continuous_projIcc
    have hmclip r : Measurable (fun ω => (Cv ω ∘ intervalClamp 0 d hd) r) :=
      (hC.adapted P F hX hY _ (hbelow _ (intervalClamp_mem 0 d hd r))).mono (hle _) le_rfl
    exact continuous_signed_stieltjes_totalVariation_measurable _ hclip hmclip
      (fun ω => intervalClamp_boundedVariation 0 d hd (Cv ω)
        (hC.variation.finite_boundedVariation F ω d hd hdT)) 0
  · intro s t
    by_cases hst : s ≤ t
    · have he ω : ν ω (Ioc s t) = Cv ω (intervalClamp 0 d hd t)-Cv ω (intervalClamp 0 d hd s) :=
        bvSigned_Ioc _ _ _ _ s t hst
      simp only [he]
      exact ((hC.adapted P F hX hY _ (hbelow _ (intervalClamp_mem 0 d hd t))).mono (hle _) le_rfl).sub
        ((hC.adapted P F hX hY _ (hbelow _ (intervalClamp_mem 0 d hd s))).mono (hle _) le_rfl)
    · simp only [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hst)),VectorMeasure.empty]
      exact measurable_const
  · filter_upwards [hcs] with ω hω
    letI : IsFiniteMeasure (α ω) := intervalStieltjes_finite _ _ _ _ _ _
    letI : IsFiniteMeasure (β ω) := intervalStieltjes_finite _ _ _ _ _ _
    apply signed_cs_absolute_continuity (α ω) (β ω) (ν ω) hω
    have hs := interval_stieltjes_ae_mem_Ioc 0 d hd (fun r => A (realTimeClamp r) ω) (hAm ω)
      (fun r hr => (hAc ω r hr).mono inter_subset_left)
    have hz : ∀ᵐ r ∂α ω, r ∉ Iic (0:ℝ) := by
      filter_upwards [hs] with r hr
      exact not_le.mpr hr.1
    simpa only [not_not,setOf_mem_eq] using ae_iff.mp hz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.canonical_covariance_measure_fubini_data
