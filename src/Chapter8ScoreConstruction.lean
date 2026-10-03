import Chapter8ContinuousScoreCross
import Chapter8LongTimeMatrixBracketCLT

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
  Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Construct the vector score and its full information-matrix bracket
from continuous adapted coefficients, allowing their linear growth. -/
theorem score_martingales_constructed {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (H : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j (t : ℝ),Measurable[B.F (realTimeClamp t)] (H k j (realTimeClamp t)))
    (hHc : ∀ k j w,Continuous (fun t : ℝ => H k j (realTimeClamp t) w)) :
    ∃ (N : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
      (C : Fin p → Fin p → HalfClosedTime → Ω → ℝ),
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => H k j (realTimeClamp z.2) z.1) (N k j)) ∧
      (∀ k,LocalMProcessWitness P B.F (fun t w => ∑ j,N k j t w)) ∧
      (∀ k l,LocalCovarianceWitness P B.F (fun t w => ∑ j,N k j t w)
        (fun t w => ∑ j,N l j t w) (C k l)) ∧
      ∀ k l b,0≤b → C k l (realTimeClamp b)=ᵐ[P]
        fun w => ∫ r in 0..b,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w := by
  let G := fun k j (z : Ω × ℝ) => H k j (realTimeClamp z.2) z.1
  have hGr k j w : Continuous (fun r => G k j (w,r)) :=
    hHc k j w
  have hGm k j : Measurable (G k j) := by
    have hm r : Measurable (H k j (realTimeClamp r)) := (hHa k j _).mono (B.le _) le_rfl
    simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using
      (measurable_uncurry_of_continuous_of_measurable (hGr k j) hm).comp measurable_swap
  have hGp k j r (hr : 0<r) := continuous_adapted_real_progressive B.F B.mono (G k j) r hr.le
    (fun s _ => hHa k j _) (fun w => (hGr k j w).continuousOn)
  choose N hN hNI using fun k => continuous_vector_integrals_constructed P B (G k) (hGm k) (hGp k) (hGr k)
  choose C hC hCe using fun k l => continuous_score_cross P B (G k) (G l) (hGm k) (hGm l)
    (hGr k) (hGr l) (N k) (N l) (hN k) (hN l) (hNI k) (hNI l)
  exact ⟨N,C,hN,hNI,fun k => local_martingale_finset_sum P (by simp) B.F B.mono B.le
    Finset.univ (N k) (fun j _ => hN k j),hC,hCe⟩

end Asakura.Chapter8
