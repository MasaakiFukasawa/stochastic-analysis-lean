import Chapter3MultivariatePathLimit
import Chapter3ScalarIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's full finite-dimensional C² Ito formula. The partition,
its derivative bounds, all three approximation limits, compact Taylor
control and removal of the finite horizon are derived in this proof. -/
theorem multivariate_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M Z : Fin d → ClosedTime T → Ω → ℝ)
    (C J : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hZ : ∀ i, SemimartingaleIntegralFormula P F c hc (A i) (M i)
      (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i))
    (hJ : ∀ i j, VariationIntegralFormula P c hc (C i j)
      (fun z => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp z.2) z.1)
        (Pi.single i 1) (Pi.single j 1)) (J i j)) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      f (fun i => X i t ω) = f (fun i => X i ⊥ ω)+
        (∑ i, Z i t ω)+(∑ i, ∑ j, J i j t ω)/2 := by
  classical
  let W := fun t ω i => X i t ω
  have hXm i t (ht : t < ⊤) : Measurable[F t] (X i t) := by
    have heq : X i t = fun ω => A i t ω+M i t ω := funext ((hX i).decomposition t ht)
    rw [heq]
    exact ((hX i).variation.adapted t ht).add ((hX i).martingale.adapted P F t ht)
  have hWm t (ht : t < ⊤) : Measurable[F t] (W t) := by
    letI : MeasurableSpace Ω := F t
    exact Measurable.of_eval (fun i => hXm i t ht)
  have hWc ω t (ht : t < ⊤) : ContinuousAt (fun s => W s ω) t :=
    continuousAt_pi.mpr (fun i => (hX i).continuous ω t ht)
  let D := fun i t ω => fderiv ℝ f (W t ω) (Pi.single i 1)
  let E := fun i j t ω => fderiv ℝ (fderiv ℝ f) (W t ω) (Pi.single i 1) (Pi.single j 1)
  have hdf := hf.continuous_fderiv (by norm_num)
  have hddf := (hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1 ≤ 2)).continuous_fderiv (by norm_num)
  have hdfi i : Continuous (fun x => fderiv ℝ f x (Pi.single i 1)) := hdf.clm_apply continuous_const
  have hddfij i j : Continuous (fun x => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) :=
    (hddf.clm_apply continuous_const).clm_apply continuous_const
  have hdm i t (ht : t < ⊤) : Measurable[F t] (D i t) := (hdfi i).measurable.comp (hWm t ht)
  have hem i j t (ht : t < ⊤) : Measurable[F t] (E i j t) := (hddfij i j).measurable.comp (hWm t ht)
  have hdc i ω t (ht : t < ⊤) : ContinuousAt (fun s => D i s ω) t :=
    (hdfi i).continuousAt.comp (hWc ω t ht)
  have hec i j ω t (ht : t < ⊤) : ContinuousAt (fun s => E i j s ω) t :=
    (hddfij i j).continuousAt.comp (hWc ω t ht)
  let V : ((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ (Fin d × Fin d))) → ClosedTime T → Ω → ℝ :=
    Sum.elim (Sum.elim A M) (Sum.elim D (fun p => E p.1 p.2))
  have hVm i t (ht : t < ⊤) : Measurable[F t] (V i t) := by
    rcases i with (i|i)
    · rcases i with (i|i)
      · exact (hX i).variation.adapted t ht
      · exact (hX i).martingale.adapted P F t ht
    · rcases i with (i|⟨i,j⟩)
      · exact hdm i t ht
      · exact hem i j t ht
  have hVc i ω t (ht : t < ⊤) : ContinuousAt (fun s => V i s ω) t := by
    rcases i with (i|i)
    · rcases i with (i|i)
      · exact (hX i).variation_continuous P F ω t ht
      · exact (hX i).martingale.path P F ω t ht
    · rcases i with (i|⟨i,j⟩)
      · exact hdc i ω t ht
      · exact hec i j ω t ht
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,hL⟩ := common_oscillation_partition P F hF hle V hVm hVc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hq := TopologicalSpace.denseRange_denseSeq (Iio (⊤ : ClosedTime T))
  have hLA i n j k := hL (Sum.inl (Sum.inl i)) n j (q k).val
  have hLM i n j k := hL (Sum.inl (Sum.inr i)) n j (q k).val
  have hLD i n j k := hL (Sum.inr (Sum.inl i)) n j (q k).val
  have hLE i j n l k := hL (Sum.inr (Sum.inr (i,j))) n l (q k).val
  have hct k : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  have hlu k i := semimartingale_integral_approximation P hT F hF hle hnull
    (X i) (A i) (M i) (D i) (Z i) (hX i) (hdm i) (hdc i) c hc hcT hcc (hZ i)
    τ hs hm ht h0 hco q hq (hLD i) _ (hct k)
  have hlv k i j := semimartingale_covariation_integral_approximation P hT F hF hle hnull
    (X i) (X j) (A i) (A j) (M i) (M j) (C i j) (E i j) (hX i) (hX j) (hC i j)
    (hem i j) (hec i j) τ hs hm ht h0 hco q hq
    (hLM i) (hLM j) (hLA i) (hLA j) (hLE i j) c hc hcT (J i j) (hJ i j) k
  have hlq k i : ∀ᵐ ω ∂P, ∃ Q : ClosedTime T → ℝ, TendstoUniformly
      (fun n t => partitionCross (fun s => X i s ω) (fun s => X i s ω) (fun _ => 1)
        (fun j => τ n j ω) (min (realTimeClamp (c k)) t)) Q atTop := by
    have h := semimartingale_covariation_approximation P hT F hF hle hnull
      (X i) (X i) (A i) (A i) (M i) (M i) (C i i) (fun _ _ => 1)
      (hX i) (hX i) (hC i i) (fun _ _ => measurable_const) (fun _ _ _ => continuousAt_const)
      τ hs hm ht h0 hco q hq (hLM i) (hLM i) (hLA i) (hLA i)
      (fun _ _ _ => by simp) (c k) (hc k) (hcT k)
    filter_upwards [h] with ω hω
    obtain ⟨hv,hr,hlim⟩ := hω
    exact ⟨_,hlim⟩
  filter_upwards [ae_all_iff.mpr (fun k => ae_all_iff.mpr (hlu k)),
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun i => ae_all_iff.mpr (hlv k i))),
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (hlq k))] with ω huω hvω hqω
  intro t htop
  obtain ⟨k,hk⟩ := hcc t htop
  have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
  choose Q hQ using hqω k
  have hstep n j : ‖W (min (τ n (j+1) ω) t) ω-W (min (τ n j ω) t) ω‖ ≤ 2*(1/2:ℝ)^n := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) n))).mpr
    intro i
    have h1 := hb (Sum.inl (Sum.inl i)) n j ω t
    have h2 := hb (Sum.inl (Sum.inr i)) n j ω t
    have heq : W (min (τ n (j+1) ω) t) ω i-W (min (τ n j ω) t) ω i =
        (A i (min (τ n (j+1) ω) t) ω-A i (min (τ n j ω) t) ω)+
        (M i (min (τ n (j+1) ω) t) ω-M i (min (τ n j ω) t) ω) := by
      dsimp [W]
      rw [(hX i).decomposition _ ((min_le_right _ _).trans_lt htop),
        (hX i).decomposition _ ((min_le_right _ _).trans_lt htop)]
      ring
    change ‖W (min (τ n (j+1) ω) t) ω i-W (min (τ n j ω) t) ω i‖ ≤ _
    rw [heq]
    dsimp only [V,Sum.elim_inl,Sum.elim_inr] at h1 h2
    exact (norm_add_le _ _).trans (by change _ ≤ _; linarith)
  have hη : Tendsto (fun n => 2*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).const_mul 2
  apply multivariate_ito_path_limit (fun s => W s ω) (hWc ω) f hf
    (fun n j => τ n j ω) (fun n => hm n ω) (fun n => h0 n ω) (fun n => hco n ω)
    t htop (fun n => 2*(1/2:ℝ)^n) hη hstep
    (fun i => Z i t ω) (fun i j => J i j t ω) (fun i => Q i t)
  · intro i
    simpa only [hmin,partitionLinear] using (huω k i).tendsto_at t
  · intro i j
    simpa only [hmin] using (hvω k i j).tendsto_at t
  · intro i
    simpa only [hmin] using (hQ i).tendsto_at t

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.multivariate_ito_formula
