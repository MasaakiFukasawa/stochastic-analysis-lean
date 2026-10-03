import Chapter4FiniteStepDomain
import Chapter4BrownianSystem
import Chapter7ClockHalfTime

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the actual Ito integral of a finite adapted step process,
and identify its value at the last grid point with the written sum. -/
theorem brownian_step_integral {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (j : Fin d)
    (n : ℕ) (h : ℝ) (hh : 0≤h) (G : ℕ → Ω → ℝ)
    (hGa : ∀ k∈range n,Measurable[B.F (realTimeClamp ((k:ℝ)*h))] (G k))
    (hG2 : ∀ k∈range n,MemLp (G k) 2 P) :
    let J := fun t w => ∑ k∈range n,G k w*(B.W j (min (realTimeClamp (((k:ℝ)+1)*h)) t) w-B.W j (min (realTimeClamp ((k:ℝ)*h)) t) w)
    ContinuousM2Witness P B.F J ∧ LocalMProcessWitness P B.F J ∧
    ItoCovarianceFormula P B.F (B.W j)
      (fun z => ∑ k∈range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => G k z.1) z.2) J ∧
    (∀ w,J (realTimeClamp ((n:ℝ)*h)) w=∑ k∈range n,G k w*(B.W j (realTimeClamp (((k:ℝ)+1)*h)) w-B.W j (realTimeClamp ((k:ℝ)*h)) w)) := by
  let Z := fun k t w => G k w*(B.W j (min (realTimeClamp (((k:ℝ)+1)*h)) t) w-B.W j (min (realTimeClamp ((k:ℝ)*h)) t) w)
  have hstep k (hk : k∈range n) := brownian_elementary_ito_constructed P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null (B.W j) (B.C j j) (B.martingale j) (B.cov j j)
    (fun w r hr _ => B.diagonal_clock j w r hr) (((k:ℝ)+1)*h) (by positivity) (EReal.coe_lt_top _) ((k:ℝ)*h)
    ⟨by positivity,by nlinarith⟩ (G k) (hGa k hk) (hG2 k hk)
  refine ⟨continuous_m2_finset_sum P B.F B.mono B.le (range n) Z (fun k hk => (hstep k hk).1),
    local_martingale_finset_sum P (show (0:EReal)<⊤ by simp) B.F B.mono B.le (range n) Z (fun k hk => (hstep k hk).2.1),
    finite_ito_sum P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null (B.W j) (B.martingale j) (range n) _ Z (fun k hk => (hstep k hk).2.2),?_⟩
  intro w
  apply sum_congr rfl
  intro k hk
  have hkn : (k:ℝ)+1≤n := by exact_mod_cast (show k+1≤n from mem_range.mp hk)
  have hk0 : (k:ℝ)≤n := by linarith
  rw [min_eq_left (real_time_clamp_mono (mul_le_mul_of_nonneg_right hkn hh)),
    min_eq_left (real_time_clamp_mono (mul_le_mul_of_nonneg_right hk0 hh))]

end Asakura.Chapter6
