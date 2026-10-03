import Chapter7ModulusRemainderProbability
import Chapter7DriftIntervalRemainder

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The residual after freezing the actual continuous drift at each left
endpoint, multiplied by the actual Brownian increment. -/
theorem drift_remainder_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T : ℝ) (hT : 0<T) (b : ℝ → Ω → ℝ)
    (hbc : ∀ w,Continuous (fun r => b r w))
    (hbm : ∀ r∈Icc 0 T,Measurable (b r)) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*∑ k : Fin (n+1),
      ((∫ r in (k:ℝ)*(T/(n+1))..((k:ℝ)+1)*(T/(n+1)),b r w)-
        (T/(n+1))*b ((k:ℝ)*(T/(n+1))) w)*
      (∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-
        B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w))) atTop (fun _ => 0) := by
  let f : Ω → C(Icc (0:ℝ) T,ℝ) := fun w => ⟨fun r => b r w,(hbc w).comp continuous_subtype_val⟩
  have hf r : Measurable (fun w => f w r) := hbm r r.property
  let h := fun n : ℕ => T/((n:ℝ)+1)
  let s := fun n (k : Fin (n+1)) => (k:ℝ)*h n
  let e := fun n (k : Fin (n+1)) => ((k:ℝ)+1)*h n
  let R := fun n (k : Fin (n+1)) w => (∫ r in s n k..e n k,b r w)-h n*b (s n k) w
  apply modulus_remainder_probability P B u T hT f hf R
  intro n k w
  have hh : 0≤h n := by dsimp [h]; positivity
  have hs : 0≤s n k := mul_nonneg (by positivity) hh
  have hse : s n k≤e n k := by dsimp [s,e]; nlinarith
  have he : e n k≤T := by
    have hk : (k:ℝ)+1≤(n:ℝ)+1 := by exact_mod_cast (Nat.succ_le_of_lt k.isLt)
    calc
      _ ≤ ((n:ℝ)+1)*h n := mul_le_mul_of_nonneg_right hk hh
      _ = T := by dsimp [h]; field_simp
  let a : Icc (0:ℝ) T := ⟨s n k,⟨hs,hse.trans he⟩⟩
  let z : Icc (0:ℝ) T := ⟨e n k,⟨hs.trans hse,he⟩⟩
  have hdiff : e n k-s n k=h n := by dsimp [e,s]; ring
  have hmesh : (z:ℝ)-(a:ℝ)≤(Real.toNNReal (h n):ℝ) := by
    rw [Real.coe_toNNReal _ hh]
    exact hdiff.le
  have hb := drift_interval_remainder T (fun r => b r w) (hbc w).continuousOn a z hse
    (Real.toNNReal (h n)) hmesh
  change |(∫ r in s n k..e n k,b r w)-(e n k-s n k)*b (s n k) w|≤
    (e n k-s n k)*‖modulusPath (f w) (Real.toNNReal (h n))‖ at hb
  rw [hdiff] at hb
  exact hb

end Asakura.Chapter7
