import Chapter6BoundedVectorCovariance

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

theorem bounded_vector_cross_density {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (β H : Fin d → Ω × ℝ → ℝ) (hβm : ∀ j,Measurable (β j)) (hHm : ∀ j,Measurable (H j))
    (K : ℝ) (hK : 0≤K) (hβb : ∀ j z,|β j z|≤K) (hHb : ∀ j z,|H j z|≤K)
    (N M : Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ j,LocalMProcessWitness P B.F (N j)) (hM : ∀ j,LocalMProcessWitness P B.F (M j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (β j) (N j))
    (hMI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (H j) (M j)) :
    ∃ C,LocalCovarianceWitness P B.F (fun t w => ∑ j,N j t w) (fun t w => ∑ j,M j t w) C ∧
      ∀ r : ℝ,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,∑ j,β j (w,s)*H j (w,s) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨hZ,_,L,_,hL,_,hLe⟩ := bounded_vector_integral_covariances P B β hβm K hK hβb N hN hNI
  let Z := fun t w => ∑ j,N j t w
  have hi j w r hr := bounded_time_integrable _ ((hβm j).comp measurable_prodMk_left) K (fun s => hβb j (w,s)) r hr
  have hip j w r hr := bounded_product_time_integrable _ _ ((hHm j).comp measurable_prodMk_left)
    ((hβm j).comp measurable_prodMk_left) K hK (fun s => hHb j (w,s)) (fun s => hβb j (w,s)) r hr
  have hLC j := covariance_density_common_time P B.F Z (B.W j) (L j) hZ (B.martingale j) (hL j)
    (β j) (fun r hr => ae_of_all _ (fun w => hi j w r hr)) (hLe j)
  have hex j : ∃ C,LocalCovarianceWitness P B.F (M j) Z C ∧
      ∀ r : ℝ,0≤r → C (realTimeClamp r)=ᵐ[P] fun w => ∫ s in 0..r,H j (w,s)*β j (w,s) := by
    exact measurable_ito_covariance_density P B.F (B.W j) Z (M j) (L j) hZ ((hL j).symm P B.F)
      (H j) (β j) (fun w => (hHm j).comp measurable_prodMk_left) (fun w => (hβm j).comp measurable_prodMk_left)
      (hMI j) (fun r hr => ae_of_all _ (fun w => hi j w r hr))
      (fun r hr => ae_of_all _ (fun w => hip j w r hr)) (hLC j)
  choose C hC hCe using hex
  have hsum := weighted_covariance_finset_left P hT B.F B.mono B.le univ M C Z (fun _ => 1) (fun j _ => hC j)
  refine ⟨fun t w => ∑ j,C j t w,?_,?_⟩
  · simpa only [one_mul] using hsum.symm P B.F
  · intro r hr
    filter_upwards [ae_all_iff.2 (fun j => hCe j r hr)] with w hw
    change (∑ j,C j (realTimeClamp r) w)=_
    simp_rw [hw]
    rw [intervalIntegral.integral_finsetSum (fun j _ => by simpa only [mul_comm,Function.comp_def] using hip j w r hr)]
    apply sum_congr rfl
    intro j _
    congr 1
    funext s
    ring

end Asakura.Chapter6
