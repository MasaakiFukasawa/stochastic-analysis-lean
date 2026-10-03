import Chapter7GridMartingaleClockLimit

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Applying the chapter's martingale CLT to the constructed grid integral.
The remaining terminal-value identity is separate and is not assumed here. -/
theorem brownian_grid_martingale_clt {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (Baux : BrownianSystem Q 1)
    (K : Fin d → Fin d → ℝ) (T : ℝ) (hT : 0<T) (hK : 0<∑ i,∑ j,(K i j)^2) :
    ∃ (N : ℕ → Fin d → HalfClosedTime → Ω → ℝ) (B0 : BrownianSystem (P.prod Q) 1),
      (∀ n i,LocalMProcessWitness P B.F (N n i)) ∧
      (∀ n i,ItoCovarianceFormula P B.F (B.W i)
        (fun z => (2*Real.sqrt ((n+1:ℕ):ℝ)/T)*brownianGridIntegrand B (K i) (T/(n+1)) (n+2) z) (N n i)) ∧
      TendstoInDistribution (fun n w => ∑ i,N n i (realTimeClamp T) w) atTop
        (fun z => Real.sqrt (2*(∑ i,∑ j,(K i j)^2)/T)*B0.W 0 (realTimeClamp T) z) (fun _ => P) (P.prod Q) := by
  obtain ⟨N,C,hN,hNI,hM,hC,hp⟩ := grid_martingale_clock_limit P B K T hT
  let a : ℝ≥0 := ⟨T,hT.le⟩
  have hc : 0<2*(∑ i,∑ j,(K i j)^2)/T := div_pos (mul_pos (by norm_num) hK) hT
  obtain ⟨B0,hlim⟩ := scaled_finite_time_clt P Q B.F B.mono B.le
    (fun n t w => ∑ i,N n i t w) C hM hC a _ hc
    (fun t ht => hp t t.property ht) Baux
  exact ⟨N,B0,hN,hNI,hlim⟩

end Asakura.Chapter7
