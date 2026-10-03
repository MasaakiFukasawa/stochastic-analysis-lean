import Chapter12TrimLpIsometry
import Chapter12BrownianTimeSurjective
import Chapter12AdaptedStepDensity
import Chapter12PiIsometry

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

noncomputable def brownianTimeEquiv {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) :
    Lp (FiniteWienerHilbert d T) 2 P ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (P.prod (compactTimeMeasure T hT))) :=
  LinearIsometryEquiv.ofSurjective (brownianTimeIsometry P T hT)
    (brownianTimeIsometry_surjective P T hT)

/-- Adapted square-integrable time processes are embedded isometrically
in the H-valued L2 space on which the actual divergence is defined. -/
noncomputable def adaptedWienerEmbedding {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hle : ∀ t,F t≤m) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product F hle))) →ₗᵢ[ℝ] Lp (FiniteWienerHilbert d T) 2 P := by
  letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := m.prod inferInstance
  let J := trimLpIsometry (E:=ℝ) (P.prod (compactTimeMeasure T hT)) (progressiveSpace F)
    (progressive_space_le_product F hle)
  exact (brownianTimeEquiv P T hT).symm.toLinearIsometry.comp (finitePiIsometry J)

theorem adaptedWienerEmbedding_time {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hle : ∀ t,F t≤m) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    ∀ U : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product F hle))),∀ i,
      (brownianDerivativeTime P T hT (adaptedWienerEmbedding P T hT F hle U) i : Ω × Icc (0:ℝ) T → ℝ)
        =ᵐ[P.prod (compactTimeMeasure T hT)] (U i : Ω × Icc (0:ℝ) T → ℝ) := by
  letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := m.prod inferInstance
  intro U i
  have he := (brownianTimeEquiv (d:=d) P T hT).apply_symm_apply
    (finitePiIsometry (trimLpIsometry (P.prod (compactTimeMeasure T hT)) (progressiveSpace F)
      (progressive_space_le_product F hle)) U)
  have hi := congrArg (fun v => v i) he

  change brownianDerivativeTime P T hT (adaptedWienerEmbedding P T hT F hle U) i=
    trimLpIsometry (P.prod (compactTimeMeasure T hT)) (progressiveSpace F)
      (progressive_space_le_product F hle) (U i) at hi
  rw [hi]
  exact trimLpIsometry_coe _ _ _ _

end Asakura.Chapter12
