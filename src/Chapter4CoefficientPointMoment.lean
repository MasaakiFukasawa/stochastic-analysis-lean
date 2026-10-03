import Chapter4VectorCoefficientBridge

open MeasureTheory Set
open scoped ENNReal Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma square_lipschitz_coefficient_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {dim : ℕ}
    (b : (Fin dim → ℝ) → ℝ) (L : ℝ) (hL : 0≤L)
    (hb : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (Y : Ω → Fin dim → ℝ) (hY : MemLp Y 2 P) :
    MemLp (fun w => b (Y w)) 2 P := by
  have hbc := Vector.coordinate_continuous_of_square_lipschitz b L hL hb
  have hdiff : MemLp (fun w => b (Y w)-b 0) 2 P := by
    apply (hY.norm.const_mul (Real.sqrt L)).mono'
      ((hbc.comp_aestronglyMeasurable hY.aestronglyMeasurable).sub aestronglyMeasurable_const)
    exact ae_of_all _ fun w => by
      change |b (Y w)-b 0|≤Real.sqrt L*‖Y w‖
      have hh := hb (Y w) 0
      simp only [sub_zero] at hh
      have he : (Real.sqrt L*‖Y w‖)^2=L*‖Y w‖^2 := by rw [mul_pow,Real.sq_sqrt hL]
      have hn : 0≤Real.sqrt L*‖Y w‖ := by positivity
      nlinarith [sq_abs (b (Y w)-b 0),abs_nonneg (b (Y w)-b 0)]
  convert hdiff.add (memLp_const (b 0)) using 1
  funext w
  change b (Y w)=(b (Y w)-b 0)+b 0
  ring

end Asakura.Chapter4
