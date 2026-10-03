import Chapter3PartitionEssentialBounds
import Chapter3VariationChainTaylor
import Chapter3CommonOscillationPartition
import Chapter3VariationIntegralApproximation
import Chapter2ItoConstructionChoices

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The C¹ chain rule stated before Ito's formula, for the already defined
signed Stieltjes integral of a continuous locally finite-variation process. -/
theorem continuous_variation_chain_rule
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (A I : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hI : VariationIntegralFormula P c hc A
      (fun z => deriv f (A (realTimeClamp z.2) z.1)) I) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → f (A t ω) = f (A ⊥ ω)+I t ω := by
  let H := fun t ω => deriv f (A t ω)
  have hd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hHm t (ht : t < ⊤) : Measurable[F t] (H t) := hd.measurable.comp (hA.adapted t ht)
  have hHc ω t (ht : t < ⊤) : ContinuousAt (fun s => H s ω) t := hd.continuousAt.comp (hAc ω t ht)
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,_⟩ := common_oscillation_partition P F hF hle
    (fun _ : Unit => H) (fun _ => hHm) (fun _ => hHc)
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  have ho : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n :=
    stopped_bound_interval_oscillation P H τ (fun n => (1/2:ℝ)^n)
      (fun n j => Filter.Eventually.of_forall (fun ω t => hb () n j ω t))
  have hl k := variation_integral_approximation P F hF A H I hA hHc c hc hcT hI
    τ hm h0 hco ho k
  filter_upwards [ae_all_iff.mpr hl] with ω hω
  intro t htop
  obtain ⟨k,hk⟩ := hcc t htop
  have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
  have hlim := (hω k).tendsto_at t
  simp only [hmin] at hlim
  have hBV := local_variation_bounded_on_prefix F A hA.toPathwise t htop ω
  have herr n := variation_chain_partition_bound (fun t => A t ω) (hAc ω) f hf
    (fun j => τ n j ω) (hm n ω) (h0 n ω) (hco n ω) ((1/2:ℝ)^n)
    (pow_nonneg (by norm_num) n) (fun j s => hb () n j ω s) t htop hBV
  have hz : Tendsto (fun n => |f (A t ω)-f (A ⊥ ω)-∑' j,
      H (τ n j ω) ω*(A (min (τ n (j+1) ω) t) ω-A (min (τ n j ω) t) ω)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) herr
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const
      (eVariationOn (fun s => A s ω) (Iic t)).toReal
  have hh := tendsto_nhds_unique ((tendsto_const_nhds.sub hlim).abs) hz
  have he := abs_eq_zero.mp hh
  linarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_variation_chain_rule
