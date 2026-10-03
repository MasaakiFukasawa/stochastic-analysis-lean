import Chapter4TimeSpacePathLimit
import Chapter3MultivariateIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The time-space Ito formula with precisely C1,2 regularity. The time
coordinate only contributes its first-order integral. -/
theorem c12_time_space_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (U Z0 : ClosedTime T → Ω → ℝ)
    (hU : SemimartingaleDecomposition P F U U (fun _ _ => 0))
    (hUmn : ∀ w,Monotone (fun t => U t w)) (hUn : ∀ w t,0≤U t w)
    (X A M Z : Fin d → ClosedTime T → Ω → ℝ)
    (C J : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : ℝ → (Fin d → ℝ) → ℝ) (ft : ℝ × (Fin d → ℝ) → ℝ)
    (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hft : ∀ a x,HasDerivAt (fun s => f s x) (ft (a,x)) a) (hftc : Continuous ft)
    (hdxc : Continuous (fun z : ℝ × (Fin d → ℝ) => fderiv ℝ (f z.1) z.2))
    (hhc : Continuous (fun z : ℝ × (Fin d → ℝ) => fderiv ℝ (fderiv ℝ (f z.1)) z.2))
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (hZ0 : SemimartingaleIntegralFormula P F c hc U (fun _ _ => 0)
      (fun z => ft (U (realTimeClamp z.2) z.1,fun i => X i (realTimeClamp z.2) z.1)) Z0)
    (hZ : ∀ i,SemimartingaleIntegralFormula P F c hc (A i) (M i)
      (fun z => fderiv ℝ (f (U (realTimeClamp z.2) z.1)) (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (Z i))
    (hJ : ∀ i j,VariationIntegralFormula P c hc (C i j)
      (fun z => fderiv ℝ (fderiv ℝ (f (U (realTimeClamp z.2) z.1))) (fun k => X k (realTimeClamp z.2) z.1)
        (Pi.single i 1) (Pi.single j 1)) (J i j)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → f (U t w) (fun i => X i t w)=f (U ⊥ w) (fun i => X i ⊥ w)+
      Z0 t w+(∑ i,Z i t w)+(∑ i,∑ j,J i j t w)/2 := by
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
  let D := fun i t ω => fderiv ℝ (f (U t ω)) (W t ω) (Pi.single i 1)
  let E := fun i j t ω => fderiv ℝ (fderiv ℝ (f (U t ω))) (W t ω) (Pi.single i 1) (Pi.single j 1)
  let D0 := fun t ω => ft (U t ω,W t ω)
  have hUm t (ht : t<⊤) := hU.variation.adapted t ht
  have hVWm t (ht : t<⊤) : Measurable[F t] (fun w => (U t w,W t w)) := (hUm t ht).prodMk (hWm t ht)
  have hVWc w t (ht : t<⊤) := (hU.continuous w t ht).prodMk (hWc w t ht)
  have hdm i t (ht : t<⊤) : Measurable[F t] (D i t) :=
    (hdxc.clm_apply continuous_const).measurable.comp (hVWm t ht)
  have hem i j t (ht : t<⊤) : Measurable[F t] (E i j t) :=
    ((hhc.clm_apply continuous_const).clm_apply continuous_const).measurable.comp (hVWm t ht)
  have hdc i w t (ht : t<⊤) : ContinuousAt (fun s => D i s w) t :=
    (hdxc.clm_apply continuous_const).continuousAt.comp (hVWc w t ht)
  have hec i j w t (ht : t<⊤) : ContinuousAt (fun s => E i j s w) t :=
    ((hhc.clm_apply continuous_const).clm_apply continuous_const).continuousAt.comp (hVWc w t ht)
  have hd0m t (ht : t<⊤) : Measurable[F t] (D0 t) := hftc.measurable.comp (hVWm t ht)
  have hd0c w t (ht : t<⊤) : ContinuousAt (fun s => D0 s w) t := hftc.continuousAt.comp (hVWc w t ht)
  let V : (((Fin d ⊕ Fin d) ⊕ (Fin d ⊕ (Fin d × Fin d))) ⊕ Fin 2) → ClosedTime T → Ω → ℝ :=
    Sum.elim (Sum.elim (Sum.elim A M) (Sum.elim D (fun p => E p.1 p.2))) ![U,D0]
  have hVm i t (ht : t<⊤) : Measurable[F t] (V i t) := by
    rcases i with i | i
    · rcases i with i | i
      · rcases i with i | i
        · exact (hX i).variation.adapted t ht
        · exact (hX i).martingale.adapted P F t ht
      · rcases i with i | ⟨i,j⟩
        · exact hdm i t ht
        · exact hem i j t ht
    · fin_cases i
      · exact hUm t ht
      · exact hd0m t ht
  have hVc i w t (ht : t<⊤) : ContinuousAt (fun s => V i s w) t := by
    rcases i with i | i
    · rcases i with i | i
      · rcases i with i | i
        · exact (hX i).variation_continuous P F w t ht
        · exact (hX i).martingale.path P F w t ht
      · rcases i with i | ⟨i,j⟩
        · exact hdc i w t ht
        · exact hec i j w t ht
    · fin_cases i
      · exact hU.continuous w t ht
      · exact hd0c w t ht
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,hL⟩ := common_oscillation_partition P F hF hle V hVm hVc
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  let q := TopologicalSpace.denseSeq (Iio (⊤ : ClosedTime T))
  have hq := TopologicalSpace.denseRange_denseSeq (Iio (⊤ : ClosedTime T))
  have hLA i n j k := hL (Sum.inl (Sum.inl (Sum.inl i))) n j (q k).val
  have hLM i n j k := hL (Sum.inl (Sum.inl (Sum.inr i))) n j (q k).val
  have hLD i n j k := hL (Sum.inl (Sum.inr (Sum.inl i))) n j (q k).val
  have hLE i j n l k := hL (Sum.inl (Sum.inr (Sum.inr (i,j)))) n l (q k).val
  have hct k : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  have hlu0 k := semimartingale_integral_approximation P hT F hF hle hnull
    U U (fun _ _ => 0) D0 Z0 hU hd0m hd0c c hc hcT hcc hZ0
    τ hs hm ht h0 hco q hq (fun n j k => hL (Sum.inr 1) n j (q k).val) _ (hct k)
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
  filter_upwards [ae_all_iff.mpr hlu0,ae_all_iff.mpr (fun k => ae_all_iff.mpr (hlu k)),
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun i => ae_all_iff.mpr (hlv k i))),
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (hlq k))] with ω hu0ω huω hvω hqω
  intro t htop
  obtain ⟨k,hk⟩ := hcc t htop
  have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
  choose Q hQ using hqω k
  have hstep n j : ‖W (min (τ n (j+1) ω) t) ω-W (min (τ n j ω) t) ω‖ ≤ 2*(1/2:ℝ)^n := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) n))).mpr
    intro i
    have h1 := hb (Sum.inl (Sum.inl (Sum.inl i))) n j ω t
    have h2 := hb (Sum.inl (Sum.inl (Sum.inr i))) n j ω t
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
  have hUs : Continuous (fun s => U (min t s) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hU.continuous ω _ ((min_le_left _ _).trans_lt htop)).comp
      (continuous_const.min continuous_id).continuousAt
  have hXs : Continuous (fun s => W (min t s) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hWc ω _ ((min_le_left _ _).trans_lt htop)).comp
      (continuous_const.min continuous_id).continuousAt
  let Xs : C(ClosedTime T,Fin d → ℝ) := ⟨_,hXs⟩
  let R := max (U t ω) ‖Xs‖
  apply c12_time_space_path_limit (fun s => U s ω) (fun s => W s ω) f ft hf hft hftc hhc
    (fun n j => τ n j ω) (fun n => hm n ω) (fun n => h0 n ω) (fun n => hco n ω)
    t htop R (hUmn ω) (fun s hst => ⟨hUn ω s,(hUmn ω hst).trans (le_max_left _ _)⟩)
    (fun s hst => by
      have hh := Xs.norm_coe_le_norm s
      simpa only [Metric.mem_closedBall,dist_zero_right,Xs,ContinuousMap.coe_mk,min_eq_right hst] using hh.trans (le_max_right (U t ω) ‖Xs‖))
    (fun n => 2*(1/2:ℝ)^n) hη
    (fun n j => by
      have hh := hb (Sum.inr 0) n j ω t
      change ‖U (min (τ n (j+1) ω) t) ω-U (min (τ n j ω) t) ω‖≤(1/2:ℝ)^n at hh
      have ha := le_abs_self (U (min (τ n (j+1) ω) t) ω-U (min (τ n j ω) t) ω)
      rw [Real.norm_eq_abs] at hh
      linarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]) hstep
    (Z0 t ω) (fun i => Z i t ω) (fun i j => J i j t ω) (fun i => Q i t)
  · simpa only [hmin,partitionLinear] using (hu0ω k).tendsto_at t
  · intro i
    simpa only [hmin,partitionLinear] using (huω k i).tendsto_at t
  · intro i j
    simpa only [hmin] using (hvω k i j).tendsto_at t
  · intro i
    simpa only [hmin] using (hQ i).tendsto_at t

end Asakura.Chapter4
