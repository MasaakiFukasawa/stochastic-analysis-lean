import Chapter4DiscountCalculus

open MeasureTheory Set
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma continuous_nonnegative_time_extension {E : Type*} [TopologicalSpace E]
    (f : ℝ × E → ℝ) (hf : ContinuousOn f {z | 0≤z.1}) :
    Continuous (fun z : ℝ × E => f (max 0 z.1,z.2)) :=
  hf.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
    (fun z => show 0≤max 0 z.1 from le_max_left _ _)

lemma nonnegative_time_extension_eq {E : Type*} (f : ℝ × E → ℝ) (a : ℝ) (ha : 0≤a) (x : E) :
    f (max 0 a,x)=f (a,x) := by rw [max_eq_right ha]

lemma discount_factor_congr_on_interval (k l : ℝ → ℝ) (r : ℝ) (hr : 0≤r)
    (he : ∀ a∈Icc 0 r,k a=l a) : discountFactor k r=discountFactor l r := by
  dsimp only [discountFactor]
  congr 2
  apply intervalIntegral.integral_congr
  intro a ha
  exact he a (by simpa only [uIcc_of_le hr] using ha)

end Asakura.Chapter4
