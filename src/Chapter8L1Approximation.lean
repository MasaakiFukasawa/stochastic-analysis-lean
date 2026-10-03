import Chapter1WrittenL1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- First fix the truncation level, let the observation time tend to
infinity, and only then remove the truncation. No uniform rate in the
truncation level is required. -/
theorem limit_from_uniform_approximation {I : Type*} (l : Filter I)
    (E : I → ℝ) (a : ℕ → ℝ) (b : ℕ → I → ℝ)
    (hE : ∀ i, 0 ≤ E i) (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ k, Tendsto (b k) l (𝓝 0))
    (hbound : ∀ k i, E i ≤ 2*a k+b k i) : Tendsto E l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Eventually.of_forall (fun i => hc.trans_le (hE i))
  · intro ε hε
    obtain ⟨k,hk⟩ := (ha.eventually (gt_mem_nhds (show (0:ℝ)<ε/4 by positivity))).exists
    filter_upwards [(hb k).eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))] with i hi
    linarith [hbound k i]

/-- Uniform L1 approximation of the time averages and their limiting means
passes convergence from bounded truncations to the original observable. -/
theorem l1_limit_from_approximations {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter I)
    (X : I → Ω → ℝ) (Y : ℕ → I → Ω → ℝ) (c : ℝ) (d a : ℕ → ℝ)
    (hX : ∀ i, Integrable (X i) P) (hY : ∀ k i, Integrable (Y k i) P)
    (ha : Tendsto a atTop (𝓝 0))
    (hd : ∀ k, |d k-c| ≤ a k)
    (herror : ∀ k i, (∫ ω,|X i ω-Y k i ω| ∂P) ≤ a k)
    (hlim : ∀ k, Tendsto (fun i => ∫ ω,|Y k i ω-d k| ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω,|X i ω-c| ∂P) l (𝓝 0) := by
  apply limit_from_uniform_approximation l _ a
    (fun k i => ∫ ω,|Y k i ω-d k| ∂P)
    (fun i => integral_nonneg (fun ω => abs_nonneg _)) ha hlim
  intro k i
  have h1 : Integrable (fun ω => |X i ω-Y k i ω|) P := ((hX i).sub (hY k i)).abs
  have h2 : Integrable (fun ω => |Y k i ω-d k|) P := ((hY k i).sub (integrable_const _)).abs
  have hh := integral_mono (((hX i).sub (integrable_const c)).abs)
    ((h1.add h2).add (integrable_const |d k-c|)) (fun ω => by
      have htri := abs_add_three (X i ω-Y k i ω) (Y k i ω-d k) (d k-c)
      convert htri using 1 <;> simp only [Pi.sub_apply] <;> ring)
  simp only [Pi.add_apply] at hh
  rw [integral_add (f := fun ω => |X i ω-Y k i ω|+|Y k i ω-d k|) (g := fun _ => |d k-c|) (h1.add h2) (integrable_const _),integral_add h1 h2,
    integral_const,probReal_univ,one_smul] at hh
  simp only [Pi.sub_apply] at hh
  linarith [herror k i,hd k]

/-- The information matrix argument may conclude L1 convergence before
passing to convergence in probability. -/
theorem probability_of_l1_limit {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter I) (X : I → Ω → ℝ) (c : ℝ)
    (hi : ∀ i, Integrable (fun ω => X i ω-c) P)
    (hlim : Tendsto (fun i => ∫ ω,|X i ω-c| ∂P) l (𝓝 0)) :
    TendstoInMeasure P X l (fun _ => c) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have he (i : I) : eLpNorm (X i-(fun _ => c)) 1 P =
      ENNReal.ofReal (∫ ω,|X i ω-c| ∂P) := by
    change eLpNorm (fun ω => X i ω-c) 1 P = _
    rw [eLpNorm_one_eq_lintegral_enorm (hi i).aestronglyMeasurable]
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      (ofReal_integral_norm_eq_lintegral_enorm (hi i)).symm
  simp_rw [he]
  simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim

end Asakura.Chapter8
