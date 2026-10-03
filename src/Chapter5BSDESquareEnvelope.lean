import Chapter5BSDEMaximal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The preliminary maximal-integrability step in the manuscript's BSDE
estimate. An explicit integrable envelope dominates Y_t² simultaneously
at every time, using BDG and deterministic Cauchy--Schwarz. -/
theorem bsde_square_envelope
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Y M Q : ClosedTime T → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hQ : LocalCovarianceWitness P F M M Q)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (hQi : Integrable (Q (realTimeClamp R)) P) (hQ0 : ∀ᵐ w ∂P, 0 ≤ Q (realTimeClamp R) w)
    (ξ : Ω → ℝ) (hξ : MemLp ξ 2 P) (f : Ω × ℝ → ℝ)
    (hfi : ∀ᵐ w ∂P, MemLp (fun r => f (w,r)) 2 (volume.restrict (Ioc 0 R)))
    (hFe : Integrable (fun w => ∫ r in 0..R, f (w,r)^2) P)
    (he : ∀ᵐ w ∂P, ∀ t ∈ Icc 0 R,
      Y (realTimeClamp t) w = ξ w+(∫ r in t..R, f (w,r))-(M (realTimeClamp R) w-M (realTimeClamp t) w)) :
    ∃ U : Ω → ℝ, Integrable U P ∧ (∀ w, 0 ≤ U w) ∧
      (∀ᵐ w ∂P, ∀ t ∈ Icc 0 R, Y (realTimeClamp t) w^2 ≤ U w) := by
  have hRt : realTimeClamp (T := T) R < ⊤ := by
    change (realTimeClamp R : EReal) < T
    rw [real_time_clamp_eq R hR hRT.le]; exact hRT
  let S := runningMaximum M (hM.path P F) (realTimeClamp R)
  have hS : MemLp S 2 P := martingale_maximum_memLp_two P hT F hF hle hnull M Q hM hQ
    (realTimeClamp R) hRt hQi hQ0
  have hSi : Integrable (fun w => S w^2) P := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).mp hS
  have hξi : Integrable (fun w => ξ w^2) P := (memLp_two_iff_integrable_sq hξ.aestronglyMeasurable).mp hξ
  let U := fun w => 3*(ξ w^2+R*(∫ r in 0..R,f (w,r)^2)+4*S w^2)
  refine ⟨U,((hξi.add (hFe.const_mul R)).add (hSi.const_mul 4)).const_mul 3,?_,?_⟩
  · intro w
    have hp : 0 ≤ ∫ r in 0..R,f (w,r)^2 := intervalIntegral.integral_nonneg hR (fun r _ => sq_nonneg _)
    dsimp [U]
    positivity
  filter_upwards [he,hfi] with w hw hfw
  intro t ht
  have htime := tail_time_integral_square_bound R hR (fun r => f (w,r)) hfw t ht
  have hmR := (runningMaximum_bounds M (hM.path P F) (realTimeClamp R) hRt w).1 _ le_rfl
  have hmt := (runningMaximum_bounds M (hM.path P F) (realTimeClamp R) hRt w).1 _ (real_time_clamp_mono ht.2)
  have hdiff : |M (realTimeClamp R) w-M (realTimeClamp t) w| ≤ 2*S w := by
    calc
      _ ≤ |M (realTimeClamp R) w|+|M (realTimeClamp t) w| := abs_sub _ _
      _ ≤ 2*S w := by dsimp [S]; linarith
  have hsquared := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hsquared
  rw [hw t ht]
  dsimp only [U]
  have hthree (a b c : ℝ) : (a+b-c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (a+c),sq_nonneg (b+c)]
  nlinarith [hthree (ξ w) (∫ r in t..R,f (w,r)) (M (realTimeClamp R) w-M (realTimeClamp t) w)]

end Asakura.Chapter5
