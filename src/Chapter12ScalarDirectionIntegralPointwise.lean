import Chapter12HilbertLpBochnerPointwise
import Chapter12ContinuousLpFamily
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Explicit random-variable form of the integrated stock derivative.
Compact time continuity supplies Bochner integrability on both sides. -/
theorem scalar_direction_integral_pointwise
    {α Ω H : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [CompactSpace α] [T2Space α] [SecondCountableTopology α] [FirstCountableTopology α]
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure α) [IsFiniteMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (S : α × Ω → ℝ) (hSm : Measurable S) (hL : ∀ x, MemLp (fun w => S (x,w)) p P)
    (hSc : ∀ w, Continuous (fun x => S (x,w)))
    (v : α → H) (hvc : Continuous v)
    (G : Ω → ℝ) (hG : MemLp G p P)
    (hb : ∀ x, ∀ᵐ w ∂P, ‖S (x,w)‖ ≤ ‖G w‖) :
    ((∫ x,(ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp ((hL x).toLp _) ∂μ :
      Lp H p P) : Ω → H) =ᵐ[P] (fun w => ∫ x,S (x,w) • v x ∂μ) := by
  let F := fun x => (hL x).toLp (fun w => S (x,w))
  let U := fun x => (ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp (F x)
  have hFc : Continuous F := continuous_Lp_family_of_dominated_paths P p hp _ hL
    (ae_of_all P hSc) G hG hb
  let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).flip.compLpL₂ p P
  have hUc : Continuous U := B.continuous₂.comp (hvc.prodMk hFc)
  have hUi : Integrable U μ := hUc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLu (x) : MemLp (fun w => S (x,w) • v x) p P :=
    (ContinuousLinearMap.toSpanSingleton ℝ (v x)).comp_memLp' (hL x)
  have hUe (x) : (hLu x).toLp _ = U x := by
    apply Lp.ext
    filter_upwards [(hLu x).coeFn_toLp,(hL x).coeFn_toLp,
      (ContinuousLinearMap.toSpanSingleton ℝ (v x)).coeFn_compLp (F x)] with w h1 h2 h3
    change (hLu x).toLp _ w = (ContinuousLinearMap.toSpanSingleton ℝ (v x)).compLp (F x) w
    rw [h1,h3]
    change S (x,w) • v x = (hL x).toLp _ w • v x
    rw [h2]
  have hSi : ∀ w, Integrable (fun x => S (x,w) • v x) μ := fun w =>
    ((hSc w).smul hvc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := Hilbert_Lp_bochner_integral_pointwise μ P p hp2 (fun z => S z • v z.1)
    (hSm.smul (hvc.measurable.comp measurable_fst)) hLu
    (by simpa only [hUe] using hUi) hSi
  simpa only [hUe] using hh

end Asakura.Chapter12
