import Chapter9FiniteIntervalMartingale
import Chapter9StoppedGeneratorCutoff
import Chapter4DeterministicBracketLaw
import Chapter4FiniteCovarianceSum

open MeasureTheory Set
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Levy's argument for the frozen clock, retaining conditioning on the
 whole past and every vector projection. -/
theorem frozen_bracket_vector_characteristic {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (M : Fin d → HalfClosedTime → Ω → ℝ) (hM : ∀ i,LocalMProcessWitness P F (M i))
    (b : ℝ) (hb : 0≤b) (k : ℝ) (hk : 0≤k)
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j)
      (fun t _ => k*(if i=j then 1 else 0)*(finitePrefixTime b hb t).val))
    (R s : ℝ) (hs : 0≤s) (hsR : s≤R) (hRb : R≤b) (v : Fin d → ℝ) :
    P[(fun w => Complex.exp (((∑ i,v i*(M i (realTimeClamp R) w-M i (realTimeClamp s) w)):ℝ)*Complex.I))|
      F (realTimeClamp s)]=ᵐ[P] fun _ =>
        Complex.exp (-((k*(R-s)*(∑ i,(v i)^2):ℝ):ℂ)/2) := by
  classical
  let p := fun t : HalfClosedTime => (finitePrefixTime b hb t).val
  let C := fun (i j : Fin d) (t : HalfClosedTime) (_ : Ω) => k*(if i=j then 1 else 0)*p t
  let L := fun t w => ∑ i,v i*M i t w
  let A := fun t w => ∑ j,v j*(∑ i,v i*C i j t w)
  let q := fun t => k*(∑ i,(v i)^2)*p t
  have hL : LocalMProcessWitness P F L :=
    local_martingale_finset_sum P (by simp) F hF hle Finset.univ
      (fun i t w => v i*M i t w) (fun i _ => (hM i).smul P F (v i))
  have hA : LocalCovarianceWitness P F L L A := weighted_covariance_sum P (by simp) F hF hle M C v v hC
  have he t w : A t w=q t := by
    dsimp only [A,C,q]
    simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hqm : Monotone q := by
    intro u t hut
    exact mul_le_mul_of_nonneg_left (finite_prefix_time_mono b hb hut)
      (mul_nonneg hk (Finset.sum_nonneg fun i _ => sq_nonneg (v i)))
  have hR : 0≤R := hs.trans hsR
  have hh := deterministic_bracket_conditional_characteristic P (by simp) F hF hle hnull
    L A hL hA q (realTimeClamp R) (realTimeClamp s)
    (real_time_below R hR (EReal.coe_lt_top _)) (real_time_clamp_mono hsR)
    (hqm.monotoneOn _) (ae_of_all _ fun w t _ => he t w) 1
  have hpr : p (realTimeClamp R)=R := by
    dsimp only [p]
    rw [finite_prefix_time_min b R hb hR le_top,min_eq_left hRb]
  have hps : p (realTimeClamp s)=s := by
    dsimp only [p]
    rw [finite_prefix_time_min b s hb hs le_top,min_eq_left (hsR.trans hRb)]
  have hdiff : q (realTimeClamp R)-q (realTimeClamp s)=k*(R-s)*(∑ i,(v i)^2) := by
    dsimp only [q]
    rw [hpr,hps]
    ring
  have heq w : (∑ i,v i*(M i (realTimeClamp R) w-M i (realTimeClamp s) w))=
      L (realTimeClamp R) w-L (realTimeClamp s) w := by
    simp only [L,mul_sub,Finset.sum_sub_distrib]
  simp_rw [heq]
  simpa only [hdiff,Complex.ofReal_one,one_mul,one_pow,mul_one,Complex.ofReal_sub] using hh
end Asakura.Chapter9
