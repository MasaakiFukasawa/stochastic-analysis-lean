import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Revision20261101
set_option maxHeartbeats 1000000

/-- The direct survival-event proof. No uniform-integrability or entropy assumption. -/
theorem mean_one_of_survival {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : ℕ → Ω → ℝ) (Z S : Ω → ℝ)
    (hD : ∀ n, Integrable (D n) P) (hpos : ∀ n w, 0≤D n w)
    (hmean : ∀ n, (∫ w,D n w ∂P)=1)
    (hZ : Measurable Z) (hZpos : ∀ w,0≤Z w) (hS : Measurable S)
    (heq : ∀ (n : ℕ) w,S w < (n:ℝ)+1 → Z w=D n w)
    (htail : Tendsto (fun n : ℕ => ∫ w in {w | (n:ℝ)+1≤S w},D n w ∂P) atTop (𝓝 0)) :
    Integrable Z P ∧ (∫ w,Z w ∂P)=1 := by
  let E := fun n : ℕ => {w | S w < (n:ℝ)+1}
  have hE n : MeasurableSet (E n) := measurableSet_lt hS measurable_const
  let g := fun n => (E n).indicator Z
  have hg n : g n=(E n).indicator (D n) := by
    funext w
    by_cases hw : w∈E n
    · simp only [g,indicator_of_mem hw,heq n w hw]
    · simp only [g,indicator_of_notMem hw]
  have hgi n : Integrable (g n) P := by rw [hg]; exact (hD n).indicator (hE n)
  have hge n : (∫ w,g n w ∂P)=1-∫ w in {w | (n:ℝ)+1≤S w},D n w ∂P := by
    rw [hg,integral_indicator (hE n)]
    have hh := integral_add_compl (hE n) (hD n)
    have hc : (E n)ᶜ={w | (n:ℝ)+1≤S w} := by ext w; simp [E,not_lt]
    rw [hc,hmean n] at hh
    linarith
  have hgl : Tendsto (fun n => ∫ w,g n w ∂P) atTop (𝓝 1) := by
    simpa only [hge,sub_zero] using tendsto_const_nhds.sub htail
  have hgm : ∀ w,Monotone (fun n => g n w) := by
    intro w n m hnm
    by_cases hn : w∈E n
    · have hm : w∈E m := by
        change S w < (m:ℝ)+1
        have hcast : (n:ℝ)≤m := Nat.cast_le.mpr hnm
        have hsn : S w < (n:ℝ)+1 := hn
        linarith
      simp only [g,indicator_of_mem hn,indicator_of_mem hm,le_refl]
    · simp only [g,indicator_of_notMem hn]
      exact indicator_nonneg (fun _ _ => hZpos _) _
  have hgt : ∀ w,Tendsto (fun n => g n w) atTop (𝓝 (Z w)) := by
    intro w
    obtain ⟨N,hN⟩ := exists_nat_gt (S w)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hw : w∈E n := by
      dsimp [E]
      exact hN.trans_le (by exact_mod_cast (Nat.le_add_right N 1).trans (Nat.add_le_add_right hn 1))
    exact (indicator_of_mem hw Z).symm
  have hle : Tendsto (fun n => ∫⁻ w,ENNReal.ofReal (g n w) ∂P) atTop (𝓝 1) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hgl
    simpa only [Function.comp_def,ofReal_integral_eq_lintegral_ofReal (hgi _) (.of_forall (fun w =>
      indicator_nonneg (fun _ _ => hZpos _) w)), ENNReal.ofReal_one] using hh
  have hmono := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((hgi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal))
    (.of_forall (fun w n m hnm => ENNReal.ofReal_le_ofReal (hgm w hnm)))
    (.of_forall (fun w => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgt w)))
  have hmass : (∫⁻ w, ENNReal.ofReal (Z w) ∂P)=1 := tendsto_nhds_unique hmono hle
  have hZi : Integrable Z P := ⟨hZ.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (.of_forall hZpos)).mpr (by rw [hmass]; exact ENNReal.one_lt_top)⟩
  refine ⟨hZi,?_⟩
  have hh := integral_tendsto_of_tendsto_of_monotone hgi hZi (.of_forall hgm) (.of_forall hgt)
  exact tendsto_nhds_unique hh hgl
end Asakura.Revision20261101
