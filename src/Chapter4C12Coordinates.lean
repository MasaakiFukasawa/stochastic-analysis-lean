import Chapter4C12Taylor

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter4
open Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma c12_uniform_coordinate_taylor {dim : ℕ}
    (f : ℝ → (Fin dim → ℝ) → ℝ) (ft : ℝ × (Fin dim → ℝ) → ℝ)
    (hf : ∀ t,ContDiff ℝ 2 (f t))
    (hft : ∀ t x,HasDerivAt (fun s => f s x) (ft (t,x)) t) (hftc : Continuous ft)
    (hhc : Continuous (fun z : ℝ × (Fin dim → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (R ε : ℝ) (hε : 0<ε) :
    ∃ δ>0,∀ a∈Icc 0 R,∀ b∈Icc 0 R,a≤b → ∀ x∈Metric.closedBall 0 R,∀ y∈Metric.closedBall 0 R,
      b-a≤δ → ‖y-x‖≤δ →
      |f b y-f a x-ft (a,x)*(b-a)-
        (∑ i,(y i-x i)*fderiv ℝ (f a) x (Pi.single i 1))-
        (∑ i,∑ j,(y i-x i)*(y j-x j)*fderiv ℝ (fderiv ℝ (f a)) x (Pi.single i 1) (Pi.single j 1))/2|
      ≤ ε*(b-a)+(ε/2)*∑ i,(y i-x i)^2 := by
  obtain ⟨δ,hδ,he⟩ := c12_uniform_taylor f ft hf hft hftc hhc R ε hε
  refine ⟨δ,hδ,?_⟩
  intro a ha b hb hab x hx y hy hdt hxy
  have hh := he a ha b hb hab x hx y hy hdt hxy
  rw [differential_coordinate_sum,hessian_coordinate_sum] at hh
  simp only [Pi.sub_apply] at hh
  apply hh.trans
  have hn := pi_norm_sq_le_sum_sq (y-x)
  have hs := mul_le_mul_of_nonneg_left hn hε.le
  simp only [Pi.sub_apply] at hs
  linarith

end Asakura.Chapter4
