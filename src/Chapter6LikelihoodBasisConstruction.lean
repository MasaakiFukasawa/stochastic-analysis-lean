import Chapter6LikelihoodPathData
import Chapter6BoundedVectorConstruction

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem likelihood_basis_constructed {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (b : Fin n → ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : ∀ k,Continuous (b k))
    (R : ℝ) (hR : 0≤R) (K : ℝ) (hK : 0≤K) (hbb : ∀ k z,‖WithLp.toLp 2 (b k z)‖≤K) :
    ∃ N : Fin n → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => stoppedBrownianCoefficient P B (b k) R hR j (realTimeClamp z.2) z.1) (N k j)) := by
  have hex k : ∃ N : Fin d → HalfClosedTime → Ω → ℝ,
      (∀ j,LocalMProcessWitness P B.F (N j)) ∧
      (∀ j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => stoppedBrownianCoefficient P B (b k) R hR j (realTimeClamp z.2) z.1) (N j)) := by
    let H := stoppedBrownianCoefficient P B (b k) R hR
    obtain ⟨hHa,hHc,hHb,_⟩ := stopped_brownian_coefficient_regular P B (b k) (hb k) R hR K (hbb k)
    let G := fun j (z : Ω × ℝ) => H j (realTimeClamp z.2) z.1
    have hGr j w : Continuous (fun r => H j (realTimeClamp r) w) := (hHc j w).comp real_time_clamp_continuous
    have hGm j : Measurable (G j) := by
      have hm r : Measurable (H j (realTimeClamp r)) := (hHa j _).mono (B.le _) le_rfl
      simpa only [G,Function.comp_def,Function.uncurry_def,Prod.swap] using
        (measurable_uncurry_of_continuous_of_measurable (hGr j) hm).comp measurable_swap
    have hGp j r (hr : 0<r) := continuous_adapted_real_progressive B.F B.mono (G j) r hr.le
      (fun s _ => hHa j _) (fun w => (hGr j w).continuousOn)
    exact bounded_vector_integrals_constructed P B G hGm hGp K hK
      (fun j z => (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => H i (realTimeClamp z.2) z.1)) j).trans (hHb _ _))
  choose N hN hNI using hex
  exact ⟨N,hN,hNI⟩

end Asakura.Chapter6
