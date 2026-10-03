import Chapter8ScoreConstruction

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
  Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- Long-time score CLT for the constructed vector Ito integral. The
remaining probabilistic input is precisely the empirical Gram-matrix
limit, rather than an assumed martingale or assumed bracket identity. -/
theorem constructed_score_clt {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d p : ℕ} (B : BrownianSystem P d)
    (H : Fin p → Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ k j (t : ℝ),Measurable[B.F (realTimeClamp t)] (H k j (realTimeClamp t)))
    (hHc : ∀ k j w,Continuous (fun t : ℝ => H k j (realTimeClamp t) w))
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosDef)
    (havg : ∀ k l,TendstoInMeasure P
      (fun T w => (∫ r in 0..T,∑ j,H k j (realTimeClamp r) w*H l j (realTimeClamp r) w)/T)
      atTop (fun _ => S k l))
    (T : ℕ → ℝ) (hT : ∀ n,0<T n) (hTlim : Tendsto T atTop atTop) :
    ∃ N : Fin p → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ k j,LocalMProcessWitness P B.F (N k j)) ∧
      (∀ k j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => H k j (realTimeClamp z.2) z.1) (N k j)) ∧
      TendstoInDistribution
        (fun n w => WithLp.toLp 2 (fun k => (∑ j,N k j (realTimeClamp (T n)) w)/Real.sqrt (T n)))
        atTop id (fun _ => P) (multivariateGaussian 0 S) := by
  obtain ⟨N,C,hN,hNI,hZ,hC,hCe⟩ := score_martingales_constructed P B H hHa hHc
  refine ⟨N,hN,hNI,?_⟩
  apply long_time_matrix_bracket_clt P B.F B.mono B.le
    (fun k t w => ∑ j,N k j t w) C hZ hC S hS _ T hT hTlim
  intro k l
  apply (havg k l).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0:ℝ)] with b hb
  filter_upwards [hCe k l b hb] with w hw
  rw [hw]

end Asakura.Chapter8
