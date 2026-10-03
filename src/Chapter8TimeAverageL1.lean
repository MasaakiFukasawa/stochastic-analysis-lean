import Chapter8TimeAverageAlmostSure
import Chapter8SecondMomentL1

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem stationary_bounded_time_average_L1 {Ω E : Type*} [m : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (π : Measure E) [IsProbabilityMeasure π] (hπ : MemLp (fun x : E => x) 2 π)
    (Y : ℝ → Ω → E) (hmY : Measurable (fun p : Ω × ℝ => Y p.2 p.1))
    (hcY : ∀ ω, Continuous (fun t => Y t ω)) (hlaw : ∀ t, P.map (Y t) = π)
    (G : ℝ → MeasurableSpace Ω) (hG : ∀ t, G t ≤ m)
    (hYG : ∀ t, AEStronglyMeasurable[G t] (Y t) P)
    (X : ℝ → E → Ω → E) (hX : ∀ t ≥ 0, ∀ x, MemLp (X t x) 2 P)
    (κ : ℝ) (hκ : 0 < κ)
    (hLip : ∀ t ≥ 0, ∀ x y, ∀ᵐ ω ∂P,
      ‖X t x ω-X t y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖)
    (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (hCE : ∀ s ≥ 0, ∀ t, s ≤ t →
      P[(fun ω => f (Y t ω))|G s] =ᵐ[P] fun ω => ∫ η,f (X (t-s) (Y s ω) η) ∂P)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |f x| ≤ K)
    (T : ℕ → ℝ) (hT : ∀ n,0<T n) (hTlim : Tendsto T atTop atTop) :
    Tendsto (fun n => ∫ w,|timeAverage (fun t => f (Y t w)) (T n)-(∫ x,f x ∂π)| ∂P)
      atTop (nhds 0) := by
  let a := ∫ x,f x ∂π
  let Z := fun n w => timeAverage (fun t => f (Y t w)) (T n)-a
  have hm n : Measurable (Z n) :=
    (time_average_measurable (fun w t => f (Y t w))
      (hf.continuous.measurable.comp hmY) (T n) (hT n).le).sub measurable_const
  have hZ n : MemLp (Z n) 2 P := MemLp.of_bound (hm n).aestronglyMeasurable (K+|a|)
    (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add
        (time_average_abs_le (fun t => f (Y t w)) K (T n) (hT n) (fun t => hb _)) le_rfl))
  apply l1_limit_from_second_moments P atTop Z hZ
  have hl : Tendsto (fun n => (2*(L:ℝ)^2*(∫ x,‖x‖^2 ∂π)/κ)/(T n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hTlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun n => integral_nonneg (fun _ => sq_nonneg _))
  intro n
  simpa only [div_mul_eq_div_div] using
    stationary_markov_time_average P π hπ Y hmY hcY hlaw G hG hYG X hX κ (T n) hκ (hT n)
      hLip f L hf hCE

end Asakura.Chapter8
