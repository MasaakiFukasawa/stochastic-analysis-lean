import FullAuditBVClamp
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

abbrev UnitTime := Icc (0:ℝ) 1

noncomputable def uniformPartition (n j : ℕ) : UnitTime :=
  projIcc 0 1 (by norm_num) ((j:ℝ)/(n+1:ℕ))

theorem uniform_partition_mono (n : ℕ) : Monotone (uniformPartition n) := by
  intro j k hjk
  apply monotone_projIcc (by norm_num)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)

theorem uniform_partition_endpoints (n : ℕ) :
    uniformPartition n 0 = ⊥ ∧ uniformPartition n (n+1) = ⊤ := by
  constructor <;> apply Subtype.ext <;> simp [uniformPartition,projIcc,Set.Icc.coe_bot,Set.Icc.coe_top,ne_of_gt (show (0:ℝ) < n+1 by positivity)]

theorem uniform_partition_mesh (n j : ℕ) :
    dist (uniformPartition n (j+1)) (uniformPartition n j) ≤ 1/(n+1:ℕ) := by
  have h := (LipschitzWith.projIcc (a := (0:ℝ)) (b := 1) (by norm_num)).dist_le_mul
    (((j+1:ℕ):ℝ)/(n+1:ℕ)) ((j:ℝ)/(n+1:ℕ))
  calc
    _ ≤ dist (((j+1:ℕ):ℝ)/(n+1:ℕ)) ((j:ℝ)/(n+1:ℕ)) := by
      simpa only [uniformPartition,NNReal.coe_one,one_mul] using h
    _ = _ := by
      rw [Real.dist_eq,← sub_div]
      simp only [Nat.cast_add,Nat.cast_one]
      rw [show (j:ℝ)+1-j=1 by ring,abs_of_pos (by positivity)]

/-- The finite real variation sum is bounded by the actual supremum variation. -/
theorem finite_variation_real_bound {ι : Type*} [LinearOrder ι]
    (f : ι → ℝ) (hb : BoundedVariationOn f univ) (u : ℕ → ι) (hu : Monotone u) (N : ℕ) :
    (∑ j ∈ Finset.range N, |f (u (j+1))-f (u j)|) ≤ (eVariationOn f univ).toReal := by
  have h := ENNReal.toReal_mono hb (eVariationOn.sum_le (n := N) (f := f) hu (fun _ => mem_univ _))
  rw [ENNReal.toReal_sum (fun j _ => edist_ne_top _ _)] at h
  simpa only [edist_dist,Real.dist_eq,ENNReal.toReal_ofReal (abs_nonneg _)] using h

theorem finite_square_sum_bound (x : ℕ → ℝ) (N : ℕ) (a K : ℝ)
    (ha : 0 ≤ a) (hx : ∀ j < N, |x (j+1)-x j| ≤ a)
    (hv : ∑ j ∈ Finset.range N, |x (j+1)-x j| ≤ K) :
    ∑ j ∈ Finset.range N, (x (j+1)-x j)^2 ≤ a*K := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, a*|x (j+1)-x j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← sq_abs,pow_two]
      exact mul_le_mul_of_nonneg_right (hx j (Finset.mem_range.mp hj)) (abs_nonneg _)
    _ = a*∑ j ∈ Finset.range N, |x (j+1)-x j| := (Finset.mul_sum _ _ _).symm
    _ ≤ a*K := mul_le_mul_of_nonneg_left hv ha

/-- Uniform continuity and finite total variation imply vanishing square sums,
 exactly the pathwise step of the manuscript. The order isomorphism permits
 the stated compactification when the terminal time is infinite. -/
theorem continuous_bv_square_sums_zero {ι : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι]
    (ρ : UnitTime ≃o ι) (f : ι → ℝ) (hc : Continuous f) (hb : BoundedVariationOn f univ) :
    Tendsto (fun n => ∑ j ∈ Finset.range (n+1),
      (f (ρ (uniformPartition n (j+1)))-f (ρ (uniformPartition n j)))^2) atTop (𝓝 0) := by
  let K := (eVariationOn f univ).toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hu : UniformContinuous (f ∘ ρ) := CompactSpace.uniformContinuous_of_continuous (hc.comp ρ.continuous)
  have hmesh : Tendsto (fun n : ℕ => (1:ℝ)/(n+1:ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hud⟩ := Metric.uniformContinuous_iff.mp hu (ε/(K+1)) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hmesh).2 δ hδ)
  refine ⟨N,fun n hn => ?_⟩
  have hinc (j : ℕ) : |f (ρ (uniformPartition n (j+1)))-f (ρ (uniformPartition n j))| ≤ ε/(K+1) := by
    exact (show dist (f (ρ (uniformPartition n (j+1)))) (f (ρ (uniformPartition n j))) < ε/(K+1) from
      hud (lt_of_le_of_lt (uniform_partition_mesh n j) (hN n hn))).le
  have hs := finite_square_sum_bound (fun j => f (ρ (uniformPartition n j))) (n+1) (ε/(K+1)) K
    (by positivity) (fun j _ => hinc j)
    (finite_variation_real_bound f hb _ (ρ.monotone.comp (uniform_partition_mono n)) (n+1))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  apply hs.trans_lt
  have hK1 : 0 < K+1 := by positivity
  have heq : ε/(K+1)*K = ε*(K/(K+1)) := by ring
  rw [heq]
  exact mul_lt_of_lt_one_right hε ((div_lt_one hK1).mpr (by linarith))

end Asakura.FullAudit
