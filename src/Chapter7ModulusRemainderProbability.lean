import Chapter7ModulusProbability
import Chapter7BrownianGridTotalEnergy
import Chapter7DriftRemainderAlgebra
import Chapter7ProbabilityErrorAssembly
import Chapter7ScaledFiniteCLT

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma modulus_remainder_probability {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [CompactSpace E] [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (B : BrownianSystem P d) (u : Fin d → ℝ) (T : ℝ) (hT : 0<T)
    (f : Ω → C(E,ℝ)) (hf : ∀ t,Measurable (fun w => f w t))
    (R : (n : ℕ) → Fin (n+1) → Ω → ℝ)
    (hR : ∀ (n : ℕ) k w,|R n k w|≤(T/(n+1))*‖modulusPath (f w) (Real.toNNReal (T/(n+1)))‖) :
    TendstoInMeasure P (fun n w => Real.sqrt ((n+1:ℕ):ℝ)*∑ k : Fin (n+1),R n k w*
      (∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*(T/(n+1)))) w-
        B.W j (realTimeClamp ((k:ℝ)*(T/(n+1)))) w))) atTop (fun _ => 0) := by
  let h := fun n : ℕ => T/((n:ℝ)+1)
  let delta := fun n => Real.toNNReal (h n)
  let X := fun n w => ‖modulusPath (f w) (delta n)‖
  let Y := fun n (k : Fin (n+1)) w => ∑ j,u j*(B.W j (realTimeClamp (((k:ℝ)+1)*h n)) w-
      B.W j (realTimeClamp ((k:ℝ)*h n)) w)
  let V := fun n w => ∑ k : Fin (n+1),(Y n k w)^2
  have hh n : 0≤h n := by dsimp [h]; positivity
  have hd : Tendsto (fun n => (delta n:ℝ)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have he := (tendsto_inv_atTop_zero.comp hn).const_mul T
    have hdeltan n : (delta n:ℝ)=h n := Real.coe_toNNReal _ (hh n)
    simp only [hdeltan]
    simpa only [h,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_zero,Function.comp_def] using he
  have hx := modulus_probability P f hf delta hd
  have hm n : Measurable (V n) := brownian_grid_energy_measurable P B u (h n) (hh n)
  have hi n : Integrable (V n) P := (brownian_grid_total_energy P B u (h n) (hh n)).1
  have hv n w : 0≤V n w := sum_nonneg (fun _ _ => sq_nonneg _)
  have hnht n : ((n+1:ℕ):ℝ)*h n=T := by dsimp [h]; push_cast; field_simp
  have hmean n : (∫ w,V n w ∂P)=T*(∑ j,u j^2) := by
    rw [(brownian_grid_total_energy P B u (h n) (hh n)).2,hnht]
  have hp := probability_sqrt_energy P X V hx hm hi hv (T*(∑ j,u j^2))
    (mul_nonneg hT.le (sum_nonneg (fun _ _ => sq_nonneg _))) (fun n => (hmean n).le)
  have hpc := probability_const_mul P _ _ hp T
  simp only [mul_zero] at hpc
  apply probability_of_abs_le P _ _ hpc
  intro n
  exact ae_of_all P (fun w => by
    have hb := drift_remainder_cauchy_schwarz (fun k => R n k w) (fun k => Y n k w) (h n) (X n w)
      (hh n) (norm_nonneg _) (hR n · w)
    rw [hnht] at hb
    simpa only [X,Y,V,h,delta,abs_norm,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg hT.le,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),mul_assoc] using hb)

end Asakura.Chapter7
