import Chapter12AdaptedDivergenceAssembly

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem finitePiInjection_sum {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (U : PiLp 2 (fun _ : ι => E)) :
    ∑ i,finitePiInjection i (U i)=U := by
  apply PiLp.ext
  intro j
  change (PiLp.proj (𝕜:=ℝ) 2 (fun _ : ι => E) j) (∑ i,finitePiInjection i (U i))=U j
  rw [map_sum]
  change (∑ i,finitePiInjection i (U i) j)=U j
  simp [finitePiInjection_apply]

/-- Combining the coordinate integrals gives the vector Brownian integral
of the full adapted process in the same divergence domain. -/
theorem adapted_vector_divergence {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp (FiniteWienerHilbert d T) 2 P) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    ∀ I : Fin (d+1) → Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product F hle)) →L[ℝ] Lp ℝ 2 P,
    (∀ i U,IsDivergence D (adaptedWienerEmbedding P T hT F hle (finitePiInjection i U)) (I i U)) →
    ∀ U : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product F hle))),
      IsDivergence D (adaptedWienerEmbedding P T hT F hle U) (∑ i,I i (U i)) := by
  intro I hI U f
  have he : adaptedWienerEmbedding P T hT F hle U =
      ∑ i,adaptedWienerEmbedding P T hT F hle (finitePiInjection i (U i)) := by
    rw [←map_sum,finitePiInjection_sum]
  rw [he,inner_sum,inner_sum]
  exact Finset.sum_congr rfl (fun i _ => hI i (U i) f)

end Asakura.Chapter12
