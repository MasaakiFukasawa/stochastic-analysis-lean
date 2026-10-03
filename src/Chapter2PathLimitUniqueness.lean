import Chapter2PathMetricSeparation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Limits of two approximation sequences agree almost surely when the
distance between their corresponding terms tends to zero. -/
theorem expected_path_limits_equal
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (Z W : ℕ → Ω → C(D,ℝ)) (Y Y' : Ω → C(D,ℝ))
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    (hY : Measurable Y) (hY' : Measurable Y')
    (hZY : Tendsto (fun n => ∫ ω, pathDistance K (Z n ω) (Y ω) ∂P) atTop (𝓝 0))
    (hWY : Tendsto (fun n => ∫ ω, pathDistance K (W n ω) (Y' ω) ∂P) atTop (𝓝 0))
    (hZW : Tendsto (fun n => ∫ ω, pathDistance K (Z n ω) (W n ω) ∂P) atTop (𝓝 0)) :
    Y =ᵐ[P] Y' := by
  have hb n : (∫ ω, pathDistance K (Y ω) (Y' ω) ∂P) ≤
      (∫ ω, pathDistance K (Z n ω) (Y ω) ∂P)+
      (∫ ω, pathDistance K (Z n ω) (W n ω) ∂P)+
      (∫ ω, pathDistance K (W n ω) (Y' ω) ∂P) := by
    have hiZY := integrable_path_distance P K (Z n) Y (hZ n) hY
    have hiZW := integrable_path_distance P K (Z n) (W n) (hZ n) (hW n)
    have hiWY := integrable_path_distance P K (W n) Y' (hW n) hY'
    have h := integral_mono (integrable_path_distance P K Y Y' hY hY') ((hiZY.add hiZW).add hiWY)
      (fun ω => by
        have h1 := path_distance_triangle K (Y ω) (Z n ω) (Y' ω)
        have h2 := path_distance_triangle K (Z n ω) (W n ω) (Y' ω)
        rw [path_distance_symm K (Y ω) (Z n ω)] at h1
        change pathDistance K (Y ω) (Y' ω) ≤
          (pathDistance K (Z n ω) (Y ω)+pathDistance K (Z n ω) (W n ω))+pathDistance K (W n ω) (Y' ω)
        linarith)
    change (∫ ω, pathDistance K (Y ω) (Y' ω) ∂P) ≤
      ∫ ω, (pathDistance K (Z n ω) (Y ω)+pathDistance K (Z n ω) (W n ω))+pathDistance K (W n ω) (Y' ω) ∂P at h
    have hAdd := integral_add (hiZY.add hiZW) hiWY
    have hAdd2 := integral_add hiZY hiZW
    simp only [Pi.add_apply] at hAdd hAdd2
    rw [hAdd,hAdd2] at h
    exact h
  have hl := (hZY.add hZW).add hWY
  simp only [zero_add] at hl
  have hle := ge_of_tendsto' hl hb
  apply (expected_path_distance_zero_iff P K Y Y' hY hY').1
  exact le_antisymm hle (integral_nonneg (fun ω => (path_distance_bounds K (Y ω) (Y' ω)).1))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.expected_path_limits_equal
