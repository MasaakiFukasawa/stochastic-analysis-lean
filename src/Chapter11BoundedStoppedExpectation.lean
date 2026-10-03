import Chapter11BarrierConditional

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- The compact stopped martingales have the same mean, and a bounded
 almost sure limit retains that mean. Measurability of the limit is derived. -/
theorem bounded_stopped_expectation_limit {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (hle : ∀ t,F t≤m) (N : ℕ → HalfClosedTime → Ω → ℝ)
    (hN : ∀ n,ContinuousM2Witness P F (N n)) (t : HalfClosedTime)
    (Z : ℕ → Ω → ℝ) (Y : Ω → ℝ) (a K : ℝ)
    (he : ∀ n,Z n=ᵐ[P] fun w => a+N n t w)
    (hb : ∀ n,∀ᵐ w ∂P,|Z n w|≤K)
    (hc : ∀ᵐ w ∂P,Tendsto (fun n => Z n w) atTop (𝓝 (Y w))) :
    Integrable Y P ∧ (∫ w,Y w ∂P)=a := by
  have hi n := ((hN n).moment t).integrable (by norm_num : (1:ENNReal)≤2)
  have hm n : AEStronglyMeasurable (Z n) P :=
    ((integrable_const a).add (hi n)).aestronglyMeasurable.congr (he n).symm
  have hYm := aestronglyMeasurable_of_tendsto_ae atTop hm hc
  have hyb : ∀ᵐ w ∂P,|Y w|≤K := by
    filter_upwards [hc,ae_all_iff.mpr hb] with w hw hb
    exact le_of_tendsto hw.abs (Eventually.of_forall hb)
  have hYi : Integrable Y P := Integrable.of_bound hYm K
    (hyb.mono fun w hw => by simpa only [Real.norm_eq_abs] using hw)
  have hmean n : (∫ w,Z n w ∂P)=a := by
    have hz := integral_congr_ae (((hN n).martingale ⊥ t bot_le).trans (hN n).initial)
    rw [integral_condExp (hle ⊥)] at hz
    have hz' : (∫ w,N n t w ∂P)=0 := by simpa only [Pi.zero_apply,integral_zero] using hz
    rw [integral_congr_ae (he n),integral_add (integrable_const a) (hi n),hz']
    simp
  have hl := tendsto_integral_of_dominated_convergence (fun _ : Ω => K) hm (integrable_const K)
    (fun n => (hb n).mono fun w hw => by simpa only [Real.norm_eq_abs] using hw) hc
  refine ⟨hYi,?_⟩
  exact tendsto_nhds_unique hl (by simpa only [hmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)))

end Asakura.Chapter11
