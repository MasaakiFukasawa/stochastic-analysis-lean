import Chapter13LocallySquareRowCovariance

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the matrix stochastic integral and all entries of its bracket
from locally square-integrable progressive coefficients. -/
theorem matrix_noise_constructed {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {n d:ℕ} (B:BrownianSystem P d)
    (S:Fin n → Fin d → Ω × ℝ → ℝ) (hm:∀i j,Measurable (S i j))
    (hp:∀i j b,0<b → @Measurable _ _
      (progressiveSpace (fun t:Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) b => S i j (z.1,z.2.val)))
    (hi:∀i j w b,0≤b → IntervalIntegrable (fun r => S i j (w,r)^2) volume 0 b) :
    ∃N:Fin n → Fin d → HalfClosedTime → Ω → ℝ,
      (∀i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀i j,ItoCovarianceFormula P B.F (B.W j) (S i j) (N i j)) ∧
      ∀i k,∃C,LocalCovarianceWitness P B.F (fun t w => ∑j,N i j t w) (fun t w => ∑j,N k j t w) C ∧
        ∀b,0≤b → C (realTimeClamp b)=ᵐ[P] (fun w => ∫r in 0..b,∑j,S i j (w,r)*S k j (w,r)) := by
  have hT:(0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩:=positive_real_time_exhaustion hT
  have hex i j:∃N,LocalMProcessWitness P B.F N ∧ ItoCovarianceFormula P B.F (B.W j) (S i j) N := by
    apply brownian_local_path_energy_integral_constructed P hT B.F B.mono B.le B.null
      (B.W j) (B.C j j) (B.martingale j) (B.cov j j) c hc hcm hcT hct hcut hcc
    · intro k w r hr
      exact B.diagonal_clock j w r hr.1
    · exact hm i j
    · exact fun k => hp i j (c k) (hc k)
    · exact fun k => ae_of_all _ fun w => hi i j w (c k) (hc k).le
  choose N hN hNI using hex
  refine ⟨N,hN,hNI,?_⟩
  intro i k
  exact locally_square_row_cross_covariance P B (S i) (S k) (hm i) (hm k) (hi i) (hi k)
    (N i) (N k) (hN i) (hN k) (hNI i) (hNI k)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.matrix_noise_constructed
