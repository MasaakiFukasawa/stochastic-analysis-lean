import Chapter12ConditionalLp

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The conditional expectation at a fixed time preserves every L2 test
measurable at that time, with the statement expressed as an ordinary integral. -/
theorem conditional_L2_pairing {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hle : F ≤ m)
    (u : Lp ℝ 2 P) (G : Ω → ℝ) (hGm : Measurable[F] G) (hG : MemLp G 2 P) :
    (∫ w,(condExpL2 ℝ ℝ hle u : Lp ℝ 2 P) w*G w ∂P) = ∫ w,u w*G w ∂P := by
  letI : MeasurableSpace Ω := m
  letI : Fact (F ≤ m) := ⟨hle⟩
  let A := lpMeas ℝ ℝ F 2 P
  have hg : hG.toLp G ∈ A := hGm.aestronglyMeasurable.congr hG.coeFn_toLp.symm
  have he := A.starProjection_inner_eq_zero u (hG.toLp G) hg
  rw [inner_sub_left,sub_eq_zero] at he
  have hi (v : Lp ℝ 2 P) : inner ℝ v (hG.toLp G) = ∫ w,v w*G w ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with w hw
    rw [hw]
    change G w*v w=v w*G w
    ring
  rw [hi,hi] at he
  exact he.symm

theorem conditional_raw_pairing {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hle : F ≤ m)
    (u G : Ω → ℝ) (hu : MemLp u 2 P) (hGm : Measurable[F] G) (hG : MemLp G 2 P) :
    (∫ w,P[u|F] w*G w ∂P) = ∫ w,u w*G w ∂P := by
  letI : MeasurableSpace Ω := m
  have he := conditional_L2_pairing P F hle (hu.toLp u) G hGm hG
  have hq := hu.condExpL2_ae_eq_condExp (𝕜 := ℝ) hle
  calc
    _ = ∫ w,(condExpL2 ℝ ℝ hle (hu.toLp u) : Lp ℝ 2 P) w*G w ∂P := by
      apply integral_congr_ae
      filter_upwards [hq] with w hw
      rw [hw]
    _ = ∫ w,hu.toLp u w*G w ∂P := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with w hw
      rw [hw]

end Asakura.Chapter12
