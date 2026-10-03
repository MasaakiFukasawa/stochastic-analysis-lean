import Chapter5BrownianIntegralBracket
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

/-- The common-event argument also works when continuity is known almost
everywhere, as for an indefinite integral with only pathwise L1 data. -/
theorem ae_continuous_common_time_equality
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [TopologicalSpace D] [SeparableSpace D] [Nonempty D]
    (X Y : D → Ω → ℝ)
    (hX : ∀ᵐ w ∂P, Continuous (fun t => X t w))
    (hY : ∀ᵐ w ∂P, Continuous (fun t => Y t w))
    (he : ∀ t, X t =ᵐ[P] Y t) :
    ∀ᵐ w ∂P, ∀ t, X t w = Y t w := by
  let q := denseSeq D
  have hq : ∀ᵐ w ∂P, ∀ n, X (q n) w = Y (q n) w := ae_all_iff.mpr (fun n => he (q n))
  filter_upwards [hX,hY,hq] with w hx hy hqw
  have heq := hx.ext_on (denseRange_denseSeq D) hy
    (fun t ht => by obtain ⟨n,rfl⟩ := ht; exact hqw n)
  exact congrFun heq

/-- Upgrade the bracket's deterministic-time integral identity to all
times of the finite interval simultaneously. -/
theorem bracket_primitive_common_time
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (b : ℝ) (hb : 0 ≤ b) (B : ℝ → Ω → ℝ) (G : Ω → ℝ → ℝ)
    (hc : ∀ w, ContinuousOn (fun r => B r w) (Icc 0 b))
    (hi : ∀ᵐ w ∂P, IntervalIntegrable (G w) volume 0 b)
    (he : ∀ r ∈ Icc 0 b, B r =ᵐ[P] fun w => ∫ s in 0..r, G w s) :
    ∀ᵐ w ∂P, ∀ r ∈ Icc 0 b, B r w = ∫ s in 0..r, G w s := by
  letI : Nonempty (Icc (0:ℝ) b) := ⟨⟨0,left_mem_Icc.mpr hb⟩⟩
  have hBc : ∀ᵐ w ∂P, Continuous (fun r : Icc (0:ℝ) b => B r.val w) :=
    ae_of_all _ fun w => continuousOn_iff_continuous_restrict.mp (hc w)
  have hIc : ∀ᵐ w ∂P, Continuous (fun r : Icc (0:ℝ) b => ∫ s in 0..r.val, G w s) := by
    filter_upwards [hi] with w hw
    have hco : ContinuousOn (fun r : ℝ => ∫ s in 0..r, G w s) (Icc 0 b) := by
      simpa only [uIcc_of_le hb] using intervalIntegral.continuousOn_primitive_interval' hw left_mem_uIcc
    exact continuousOn_iff_continuous_restrict.mp hco
  have hh := ae_continuous_common_time_equality P
    (fun r : Icc (0:ℝ) b => B r.val) (fun r : Icc (0:ℝ) b => fun w => ∫ s in 0..r.val, G w s)
    hBc hIc (fun r => he r.val r.property)
  exact hh.mono fun w hw r hr => hw ⟨r,hr⟩

end Asakura.Chapter5
