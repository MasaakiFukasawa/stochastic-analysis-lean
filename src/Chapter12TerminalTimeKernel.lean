import Chapter12BrownianDerivativeRealization

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem finite_terminal_time_kernel (T : ℝ) (hT : 0≤T) :
    (finiteTimeToCompact T hT (finiteTimeIntervalVector T 0 T) : Icc (0:ℝ) T → ℝ)
      =ᵐ[compactTimeMeasure T hT] (fun _ => (1:ℝ)) := by
  have hh := finite_time_compact_interval T hT ⟨0,le_rfl,hT⟩ ⟨T,hT,le_rfl⟩
  have hn : ∀ᵐ t ∂compactTimeMeasure T hT,t≠(⟨T,hT,le_rfl⟩ : Icc (0:ℝ) T) :=
    by
      rw [ae_iff]
      simpa using (measure_singleton (μ := compactTimeMeasure T hT) (⟨T,hT,le_rfl⟩ : Icc (0:ℝ) T))
  filter_upwards [hh,hn] with t ht hne
  rw [ht,indicator_of_mem]
  exact ⟨t.property.1,lt_of_le_of_ne t.property.2 hne⟩

theorem finite_terminal_scaled_time_kernel (T : ℝ) (hT : 0≤T) (a : ℝ) :
    (finiteTimeToCompact T hT (a • finiteTimeIntervalVector T 0 T) : Icc (0:ℝ) T → ℝ)
      =ᵐ[compactTimeMeasure T hT] (fun _ => a) := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul a (finiteTimeToCompact T hT (finiteTimeIntervalVector T 0 T)),
    finite_terminal_time_kernel T hT] with t ht hh
  rw [ht,Pi.smul_apply,hh,smul_eq_mul,mul_one]

/-- A terminal-time derivative with a constant time direction is represented
by that same random coefficient at almost every time. -/
theorem terminal_brownian_derivative_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T)
    (U : Lp (FiniteWienerHilbert d T) 2 P) (a : Fin (d+1) → Ω → ℝ)
    (ha : ∀ i,Measurable (a i))
    (hU : (U : Ω → FiniteWienerHilbert d T) =ᵐ[P]
      (fun w => WithLp.toLp 2 (fun i => a i w • finiteTimeIntervalVector T 0 T)))
    (i : Fin (d+1)) :
    (brownianDerivativeTime P T hT U i : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod (compactTimeMeasure T hT)]
      (fun z => a i z.1) := by
  have hc := (brownianCoordinateProjection T i).coeFn_compLp U
  have hr := timeRealization_coe P T hT ((brownianCoordinateProjection T i).compLp U)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable (brownianDerivativeTime P T hT U i)).measurable ((ha i).comp measurable_fst))).mpr
  filter_upwards [hc,hr,hU] with w hcw hrw huw
  rw [hcw,huw] at hrw
  exact hrw.trans (finite_terminal_scaled_time_kernel T hT (a i w))

end Asakura.Chapter12
