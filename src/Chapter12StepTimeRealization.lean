import Chapter12AdaptedWienerEmbedding

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem finite_interval_scaled_time_kernel (T : ℝ) (hT : 0≤T)
    (a b : Icc (0:ℝ) T) (c : ℝ) :
    (finiteTimeToCompact T hT (c • finiteTimeIntervalVector T a b) : Icc (0:ℝ) T → ℝ)
      =ᵐ[compactTimeMeasure T hT] (Ico a b).indicator (fun _ => c) := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul c (finiteTimeToCompact T hT (finiteTimeIntervalVector T a b)),
    finite_time_compact_interval T hT a b] with t ht hh
  rw [ht,Pi.smul_apply,hh,smul_eq_mul]
  by_cases hm : t∈Ico a b <;> simp [hm]

/-- The H-valued random interval direction realizes precisely the actual
bounded adapted step kernel, coordinate by coordinate. -/
theorem interval_brownian_derivative_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T)
    (a b : Icc (0:ℝ) T) (U : Lp (FiniteWienerHilbert d T) 2 P)
    (c : Fin (d+1) → Ω → ℝ) (hc : ∀ i,Measurable (c i))
    (hU : (U : Ω → FiniteWienerHilbert d T) =ᵐ[P]
      (fun w => WithLp.toLp 2 (fun i => c i w • finiteTimeIntervalVector T a b)))
    (i : Fin (d+1)) :
    (brownianDerivativeTime P T hT U i : Ω × Icc (0:ℝ) T → ℝ)
      =ᵐ[P.prod (compactTimeMeasure T hT)]
        (fun z => (Ico a b).indicator (fun _ => c i z.1) z.2) := by
  have hh := (brownianCoordinateProjection T i).coeFn_compLp U
  have hr := timeRealization_coe P T hT ((brownianCoordinateProjection T i).compLp U)
  have hm : Measurable (fun z : Ω × Icc (0:ℝ) T => (Ico a b).indicator (fun _ => c i z.1) z.2) := by
    change Measurable ((Prod.snd ⁻¹' Ico a b).indicator (fun z => c i z.1))
    exact ((hc i).comp measurable_fst).indicator (measurableSet_Ico.preimage measurable_snd)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable (brownianDerivativeTime P T hT U i)).measurable hm)).mpr
  filter_upwards [hh,hr,hU] with w hhw hrw huw
  rw [hhw,huw] at hrw
  exact hrw.trans (finite_interval_scaled_time_kernel T hT a b (c i w))

/-- Identification with the adapted embedding uses equality of the time
kernels, not a new choice of representatives or an assumed divergence law. -/
theorem adapted_embedding_eq_of_time_kernel {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (V : Lp (FiniteWienerHilbert d T) 2 P) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := Asakura.Chapter2Complete.progressiveSpace F
    ∀ U : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (Asakura.Chapter2Complete.progressive_space_le_product F hle))),
    (∀ i,(brownianDerivativeTime P T hT V i : Ω × Icc (0:ℝ) T → ℝ)
      =ᵐ[P.prod (compactTimeMeasure T hT)] (U i : Ω × Icc (0:ℝ) T → ℝ)) →
    adaptedWienerEmbedding P T hT F hle U=V := by
  intro U hU
  apply (brownianTimeIsometry P T hT).injective
  apply PiLp.ext
  intro i
  apply Lp.ext
  exact (adaptedWienerEmbedding_time P T hT F hle U i).trans (hU i).symm

end Asakura.Chapter12
