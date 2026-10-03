import Chapter7DriftSquareProbability

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Removing the actual drift changes each covariance entry by o_P(n^-1/2). -/
theorem drift_covariance_entry_negligible {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b c : ℝ → Ω → ℝ)
    (hbc : ∀ w,Continuous (fun r => b r w)) (hcc : ∀ w,Continuous (fun r => c r w))
    (hba : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (b r))
    (hca : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (c r))
    (hbb : ∀ r∈Icc 0 T,∀ w,|b r w|≤K) (hcb : ∀ r∈Icc 0 T,∀ w,|c r w|≤K) :
    let A := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),b r w
    let C := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),c r w
    let Y := fun n (k : Fin (n+1)) w => ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w)
    let Z := fun n (k : Fin (n+1)) w => ∑ j,v j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w)
    TendstoInMeasure P (fun n w => (Real.sqrt ((n+1:ℕ):ℝ)/T)*
      ((∑ k,(A n k w+Y n k w)*(C n k w+Z n k w))-(∑ k,Y n k w*Z n k w))) atTop (fun _ => 0) := by
  dsimp only
  let A := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),b r w
  let C := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),c r w
  let Y := fun n (k : Fin (n+1)) w => ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w)
  let Z := fun n (k : Fin (n+1)) w => ∑ j,v j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w)
  have hAZ := drift_brownian_cross_probability P B v T K hT hK b hbc hba hbb
  have hCY := drift_brownian_cross_probability P B u T K hT hK c hcc hca hcb
  have hAC := drift_square_probability P b c T K hT hK hbb hcb
  have hp := probability_const_mul P _ _ (probability_add_zero P _ _ (probability_add_zero P _ _ hAZ hCY) hAC) (1/T)
  simp only [mul_zero] at hp
  apply hp.congr_left
  intro n
  apply ae_of_all
  intro w
  have he : ((∑ k,(A n k w+Y n k w)*(C n k w+Z n k w))-(∑ k,Y n k w*Z n k w))=
      ((∑ k,A n k w*Z n k w)+(∑ k,C n k w*Y n k w))+(∑ k,A n k w*C n k w) := by
    rw [← sum_sub_distrib,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    ring
  change (1/T)*((Real.sqrt ((n+1:ℕ):ℝ)*(∑ k,A n k w*Z n k w)+Real.sqrt ((n+1:ℕ):ℝ)*(∑ k,C n k w*Y n k w))+
    Real.sqrt ((n+1:ℕ):ℝ)*(∑ k,A n k w*C n k w))=
    (Real.sqrt ((n+1:ℕ):ℝ)/T)*((∑ k,(A n k w+Y n k w)*(C n k w+Z n k w))-(∑ k,Y n k w*Z n k w))
  rw [he]
  ring

end Asakura.Chapter7
