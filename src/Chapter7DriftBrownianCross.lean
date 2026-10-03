import Chapter7DriftRemainderProbability
import Chapter7PredictableDriftProbability

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma grid_left_in_interval (T : ℝ) (hT : 0≤T) (n : ℕ) (k : Fin (n+1)) :
    (k:ℝ)*(T/((n:ℝ)+1)) ∈ Icc 0 T := by
  have hh : 0≤T/((n:ℝ)+1) := div_nonneg hT (by positivity)
  refine ⟨mul_nonneg (by positivity) hh,?_⟩
  have hk : (k:ℝ)≤(n:ℝ)+1 := by exact_mod_cast k.isLt.le
  calc
    _ ≤ ((n:ℝ)+1)*(T/((n:ℝ)+1)) := mul_le_mul_of_nonneg_right hk hh
    _ = T := by field_simp

/-- The full drift--Brownian cross term at the CLT scale. -/
theorem drift_brownian_cross_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T K : ℝ) (hT : 0<T) (hK : 0≤K) (b : ℝ → Ω → ℝ)
    (hbc : ∀ w,Continuous (fun r => b r w))
    (hba : ∀ r∈Icc 0 T,Measurable[B.F (realTimeClamp r)] (b r))
    (hbb : ∀ r∈Icc 0 T,∀ w,|b r w|≤K) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*∑ k : Fin (n+1),
      (∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),b r w)*
      (∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-
        B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w))) atTop (fun _ => 0) := by
  let h := fun n : ℕ => T/((n:ℝ)+1)
  let Y := fun n (k : Fin (n+1)) w => ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h n)) w-
    B.W j (realTimeClamp ((k:ℝ)*h n)) w)
  let A := fun n (k : Fin (n+1)) w => ∫ r in (k:ℝ)*h n..((k:ℝ)+1)*h n,b r w
  let b0 := fun n (k : Fin (n+1)) => b ((k:ℝ)*h n)
  have hp := predictable_drift_probability P B u T K hT hK b0
    (fun n k => hba _ (grid_left_in_interval T hT.le n k))
    (fun n k w => hbb _ (grid_left_in_interval T hT.le n k) w)
  have hr := drift_remainder_probability P B u T hT b hbc
    (fun r hr => (hba r hr).mono (B.le _) le_rfl)
  have hs := probability_add_zero P _ _ hp hr
  apply hs.congr_left
  intro n
  apply ae_of_all
  intro w
  change Real.sqrt ((n+1:ℕ):ℝ)*(∑ k,h n*b0 n k w*Y n k w)+
    Real.sqrt ((n+1:ℕ):ℝ)*(∑ k,(A n k w-h n*b0 n k w)*Y n k w)=
    Real.sqrt ((n+1:ℕ):ℝ)*(∑ k,A n k w*Y n k w)
  rw [← mul_add]
  congr 1
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  ring

end Asakura.Chapter7
