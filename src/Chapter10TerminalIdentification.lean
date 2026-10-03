import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The Fatou step at maturity: the pathwise extension and the L2 limit agree.
No almost surely convergent subsequence is introduced. -/
theorem terminal_identification {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : ℕ → Ω → ℝ) (pT V : Ω → ℝ)
    (hp : ∀ n, AEStronglyMeasurable (p n) P)
    (hT : AEStronglyMeasurable pT P) (hV : AEStronglyMeasurable V P)
    (hpath : ∀ᵐ w ∂P, Tendsto (fun n => p n w) atTop (𝓝 (pT w)))
    (hL2 : Tendsto (fun n => eLpNorm (fun w => p n w - V w) 2 P) atTop (𝓝 0)) :
    pT =ᵐ[P] V := by
  have hlim : ∀ᵐ w ∂P,
      Tendsto (fun n => p n w-V w) atTop (𝓝 (pT w-V w)) := by
    filter_upwards [hpath] with w hw
    exact hw.sub tendsto_const_nhds
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun n => (hp n).sub hV) (fun w => pT w-V w) (hT.sub hV) hlim
  simp only [Pi.sub_def] at hfatou
  rw [hL2.liminf_eq] at hfatou
  have hz : eLpNorm (fun w => pT w-V w) 2 P=0 := le_antisymm hfatou bot_le
  have he := (eLpNorm_eq_zero_iff (by norm_num : (2:ℝ≥0∞)≠0)).mp hz
  filter_upwards [he] with w hw
  exact sub_eq_zero.mp hw

end Asakura.Chapter10
