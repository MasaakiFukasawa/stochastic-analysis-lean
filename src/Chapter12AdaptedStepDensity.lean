import Chapter12TimeWeightedMeasure
import Chapter2WeightedDensity

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.Chapter2Complete Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 < T) [Fact (0 ≤ T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)

include hF
theorem time_elementary_memLp (s t : Icc (0:ℝ) T) (Z : Ω → ℝ)
    (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    MemLp (fun p : Ω × Icc (0:ℝ) T => (Ico s t).indicator (fun _ => Z p.1) p.2)
      2 ((P.prod (compactTimeMeasure T hT.le)).trim (progressive_space_le_product F hle)) := by
  have h := weighted_elementary_memLp_two P 0 T hT.le (fun _ t => t)
    (fun _ => monotone_id.monotoneOn _) (fun _ _ _ => continuous_id.continuousWithinAt)
    (fun _ => measurable_const) T (fun _ => by simp) F hF hle s t Z hZ hZinf
  simpa only [time_weighted_path_measure] using h

noncomputable def timeElementaryLp (s t : Icc (0:ℝ) T) (Z : Ω → ℝ)
    (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    Lp ℝ 2 ((P.prod (compactTimeMeasure T hT.le)).trim (progressive_space_le_product F hle)) :=
  (time_elementary_memLp P T hT F hF hle s t Z hZ hZinf).toLp _

/-- The actual past-measurable bounded step processes are dense for dt × P.
This specializes the chapter-2 Stieltjes-clock proof to the clock A(t)=t. -/
theorem time_elementary_span_dense
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    let S : Set (Lp ℝ 2 ((P.prod (compactTimeMeasure T hT.le)).trim
      (progressive_space_le_product F hle))) :=
      {J | ∃ (s t : Icc (0:ℝ) T) (Z : Ω → ℝ) (hZ : Measurable[F s] Z) (hZinf : MemLp Z ∞ P),
        (J : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[((P.prod (compactTimeMeasure T hT.le)).trim
          (progressive_space_le_product F hle))]
          (fun p => (Ico s t).indicator (fun _ => Z p.1) p.2)}
    Dense (Submodule.span ℝ S).carrier := by
  have h := weighted_elementary_span_dense P T hT (fun _ t => t)
    (fun _ => monotone_id.monotoneOn _) (fun _ _ _ => continuous_id.continuousWithinAt)
    (fun _ => measurable_const) T (fun _ => by simp) F hF hle
    (fun _ => continuous_id.continuousOn) hT.le (fun _ => measurable_const) hnull
  letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
  let μ := (weightedPathMeasure P 0 T hT.le (fun _ t => t)
    (fun _ => monotone_id.monotoneOn _) (fun _ _ _ => continuous_id.continuousWithinAt)
    (fun _ => measurable_const)).trim (progressive_space_le_product F hle)
  have hg : Dense (Submodule.span ℝ
      {J : Lp ℝ 2 μ | ∃ (s t : Icc (0:ℝ) T) (Z : Ω → ℝ),
        Measurable[F s] Z ∧ MemLp Z ∞ P ∧
        (J : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[μ]
          (fun p => (Ico s t).indicator (fun _ => Z p.1) p.2)}).carrier := by
    apply h.mono
    apply Submodule.span_mono
    rintro J ⟨s,t,Z,hZ,hZinf,rfl⟩
    refine ⟨s,t,Z,hZ,hZinf,?_⟩
    exact (weighted_elementary_memLp_two P 0 T hT.le (fun _ t => t)
      (fun _ => monotone_id.monotoneOn _) (fun _ _ _ => continuous_id.continuousWithinAt)
      (fun _ => measurable_const) T (fun _ => by simp) F hF hle s t Z hZ hZinf).coeFn_toLp
  have he := time_weighted_path_measure P T hT.le
  let Q (ν : Measure (Ω × Icc (0:ℝ) T)) : Prop := Dense (Submodule.span ℝ
      {J : Lp ℝ 2 ν | ∃ (s t : Icc (0:ℝ) T) (Z : Ω → ℝ),
        Measurable[F s] Z ∧ MemLp Z ∞ P ∧
        (J : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[ν]
          (fun p => (Ico s t).indicator (fun _ => Z p.1) p.2)}).carrier
  change Q μ at hg
  have hem : μ = (P.prod (compactTimeMeasure T hT.le)).trim
      (progressive_space_le_product F hle) := congrArg (fun ν => ν.trim
        (progressive_space_le_product F hle)) he
  have hh := Eq.mp (congrArg Q hem) hg
  simpa only [Q,exists_prop] using hh

end Asakura.Chapter12
