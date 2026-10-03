import Chapter3ItoApproximationBoundedInitial
import Chapter3InitialWeight

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Almost sure uniform convergence of the actual discrete Ito sums for
an arbitrary continuous adapted H. Initial-event truncation removes the
last boundedness assumption, and quadratic-variation localization removes
all moment assumptions. -/
theorem general_ito_approximation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A H Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ℝ) (hc : ∀ j, 0 < c j) (hcm : StrictMono c) (hcT : ∀ j, (c j:EReal) < T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j, realTimeClamp (T := T) (c j) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ j, t < realTimeClamp (T := T) (c j))
    (hAm : ∀ j ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c j)))
    (hAc : ∀ j ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c j)))
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτt : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (hosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n)
    (b : ClosedTime T) (hb : b < ⊤) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω*
        (X (min (τ n (j+1) ω) (min b t)) ω-X (min (τ n j ω) (min b t)) ω))
      (fun t => Y (min b t) ω) atTop := by
  let I := fun (k : ℕ) => {ω | |H ⊥ ω| ≤ (k:ℝ)}.indicator (fun _ => (1:ℝ))
  have hIm k : Measurable[F ⊥] (I k) := by
    letI : MeasurableSpace Ω := F ⊥
    apply measurable_const.indicator
    exact measurableSet_le (by simpa only [Real.norm_eq_abs] using (hHm ⊥ hT).norm) measurable_const
  have hIb k : MemLp (I k) ∞ P := by
    apply memLp_top_of_bound ((hIm k).mono (hle ⊥) le_rfl).aestronglyMeasurable 1
    exact .of_forall (fun ω => by
      by_cases h : |H ⊥ ω| ≤ (k:ℝ) <;> simp [I,Set.indicator,h])
  let Hk := fun k t ω => I k ω*H t ω
  let Yk := fun k t ω => I k ω*Y t ω
  have hHkm k t ht : Measurable[F t] (Hk k t) := (hIm k |>.mono (hF bot_le) le_rfl).mul (hHm t ht)
  have hHkc k ω t ht : ContinuousAt (fun s => Hk k s ω) t := continuousAt_const.mul (hHc ω t ht)
  have hHkb k : ∀ᵐ ω ∂P, |Hk k ⊥ ω| ≤ (k:ℝ) := .of_forall (fun ω => by
    by_cases h : |H ⊥ ω| ≤ (k:ℝ)
    · simpa only [Hk,I,Set.indicator,mem_setOf_eq,if_pos h,one_mul] using h
    · simp only [Hk,I,Set.indicator,mem_setOf_eq,if_neg h,zero_mul,abs_zero]
      exact Nat.cast_nonneg k)
  have hYk k := bounded_initial_weight_local P F hF hle Y hY (I k) (hIm k) (hIb k)
  have hYkI k := bounded_initial_weight_ito_formula P F hF hle X Y
    (fun z => H (realTimeClamp z.2) z.1) hYI (I k) (hIm k) (hIb k)
  have hoscK k : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |Hk k (τ n j ω) ω-Hk k t ω| ≤ (1/2:ℝ)^n := by
    filter_upwards [hosc] with ω hω
    intro n j t ht hu
    by_cases h : |H ⊥ ω| ≤ (k:ℝ)
    · simpa only [Hk,I,Set.indicator,mem_setOf_eq,if_pos h,one_mul] using hω n j t ht hu
    · simp only [Hk,I,Set.indicator,mem_setOf_eq,if_neg h,zero_mul,sub_self,abs_zero]
      exact pow_nonneg (by norm_num) n
  have happ k := ito_approximation_bounded_initial P hT F hF hle hnull X A (Hk k) (Yk k)
    hX hA (hYk k) (hYkI k) (hHkm k) (hHkc k) k (hHkb k)
    c hc hcm hcT hct hcut hcc hAm hAc hA0 τ hτ hτm hτt hτ0 hτc (hoscK k) b hb
  choose hEc hconv using happ
  filter_upwards [ae_all_iff.mpr hconv] with ω hω
  obtain ⟨k,hk⟩ := exists_nat_ge |H ⊥ ω|
  have hn : Tendsto (fun n => ‖continuousPath
      (fun t ω => Yk k (min b t) ω-∑' j, Hk k (τ n j ω) ω*
        (X (min (τ n (j+1) ω) (min b t)) ω-X (min (τ n j ω) (min b t)) ω)) (hEc k n) ω‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (hω k).norm
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hn.eventually (gt_mem_nhds hε)] with n hnω
  intro t
  have hb := (continuousPath _ (hEc k n) ω).norm_coe_le_norm t
  have hh := hb.trans_lt hnω
  simpa only [continuousPath,ContinuousMap.coe_mk,Yk,Hk,I,Set.indicator,mem_setOf_eq,if_pos hk,one_mul,
    Real.norm_eq_abs,Real.dist_eq,abs_sub_comm] using hh

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.general_ito_approximation
