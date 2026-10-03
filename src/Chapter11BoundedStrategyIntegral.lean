import Chapter6BoundedVectorConstruction
import Chapter6BoundedClockExponential
import Chapter2StoppedM2Equivalence
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped BigOperators
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Bounded progressively measurable strategies, without path continuity:
construct the actual Ito integral, its bracket, and the finite-horizon M2
property needed in the utility proofs. -/
theorem bounded_strategy_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hHp : ∀ b,0<b → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val)))
    (K : ℝ) (hK : 0≤K) (hHb : ∀ z,|H z|≤K) :
    ∃ N C : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P B.F N ∧ ItoCovarianceFormula P B.F (B.W 0) H N ∧
      LocalCovarianceWitness P B.F N N C ∧
      (∀ R,0≤R → C (realTimeClamp R)=ᵐ[P] fun w => ∫ s in 0..R,(H (w,s))^2) ∧
      (∀ R,0≤R → ∀ᵐ w ∂P,0≤C (realTimeClamp R) w ∧ C (realTimeClamp R) w≤K^2*R) ∧
      (∀ R,0≤R → ContinuousM2Witness P B.F (fun t w => N (min (realTimeClamp R) t) w)) ∧
      ∀ R,0≤R → Integrable (N (realTimeClamp R)) P ∧ (∫ w,N (realTimeClamp R) w ∂P)=0 := by
  obtain ⟨N,hN,hNI⟩ := bounded_vector_integrals_constructed P B (fun _ => H)
    (fun _ => hHm) (fun _ => hHp) K hK (fun _ => hHb)
  obtain ⟨_,C,L,hC,_,hCe,_⟩ := bounded_vector_integral_covariances P B (fun _ => H)
    (fun _ => hHm) K hK (fun _ => hHb) N hN hNI
  have hC' : LocalCovarianceWitness P B.F (N 0) (N 0) C := by
    simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hC
  have hCe' R (hR : 0≤R) : C (realTimeClamp R)=ᵐ[P] fun w => ∫ s in 0..R,(H (w,s))^2 := by
    simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hCe R hR
  have hb R (hR : 0≤R) : ∀ᵐ w ∂P,0≤C (realTimeClamp R) w ∧ C (realTimeClamp R) w≤K^2*R := by
    have hu := bounded_vector_clock_upper P (fun _ : Fin 1 => H) (fun _ => hHm) K hK
      (fun _ => hHb) C R hR (hCe R hR)
    filter_upwards [hCe' R hR,hu] with w he hu
    refine ⟨?_,by simpa using hu⟩
    rw [he]
    exact intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)
  have hM R (hR : 0≤R) : ContinuousM2Witness P B.F (fun t w => N 0 (min (realTimeClamp R) t) w) := by
    have hc : Measurable (C (realTimeClamp R)) :=
      ((covariance_adapted_variation P B.F B.mono B.le (hN 0) (hN 0) hC').adapted _
        (real_time_below R hR (EReal.coe_lt_top R))).mono (B.le _) le_rfl
    have hi : Integrable (C (realTimeClamp R)) P := Integrable.of_bound hc.aestronglyMeasurable (K^2*R)
      ((hb R hR).mono (fun w hw => by simpa only [Real.norm_eq_abs,abs_of_nonneg hw.1] using hw.2))
    have hs t : MeasurableSet[B.F t] {w : Ω | realTimeClamp (T := (⊤:EReal)) R≤t} := by
      by_cases h : realTimeClamp (T := (⊤:EReal)) R≤t <;> simp [h]
    have he := stopped_local_M2_equivalences P B.F B.mono B.le B.null (N 0) C (hN 0) hC'
      (fun _ => realTimeClamp R) hs (fun _ => real_time_below R hR (EReal.coe_lt_top R))
    exact he.2.mp (he.1.mp hi)
  refine ⟨N 0,C,hN 0,hNI 0,hC',hCe',hb,hM,?_⟩
  intro R hR
  have hi : Integrable (N 0 (realTimeClamp R)) P := by
    simpa only [min_self] using ((hM R hR).moment (realTimeClamp R)).integrable (by norm_num)
  have he := ((hM R hR).martingale ⊥ (realTimeClamp R) bot_le).trans (hM R hR).initial
  have hh := integral_congr_ae he
  rw [integral_condExp (B.le ⊥)] at hh
  exact ⟨hi,by simpa only [min_self,Pi.zero_apply,integral_zero] using hh⟩

end Asakura.Chapter11
