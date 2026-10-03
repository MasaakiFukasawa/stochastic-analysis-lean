import FullAuditBVMartingaleStopped

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-- The final uniform-zero step uses the checked continuous-time Doob bound,
 so the null set is common to all (uncountably many) times. -/
theorem continuous_zero_marginals_doob {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (Y : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[m] (Y t))
    (hc : ∀ ω, Continuous (fun t => Y t ω)) (hz : ∀ t, Y t =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω = 0 := by
  have h2 (t) : MemLp (Y t) 2 P := (memLp_congr_ae (hz t)).mpr MemLp.zero
  have hmart (s t : ClosedTime T) (_ : s ≤ t) : P[Y t | m] =ᵐ[P] Y s := by
    have h := condExp_congr_ae (m := m) (hz t)
    simp only [condExp_zero] at h
    exact h.trans (hz s).symm
  have hn : eLpNorm (continuousPath Y hc) 2 P ≤ 2*eLpNorm (Y ⊤) 2 P :=
    continuous_martingale_path_norm (T := T) P (fun _ => m) monotone_const (fun _ => le_rfl)
    Y hm h2 hc hmart
  rw [eLpNorm_congr_ae (hz ⊤),eLpNorm_zero,mul_zero] at hn
  have hzpath : continuousPath Y hc =ᵐ[P] 0 :=
    (eLpNorm_eq_zero_iff (f := continuousPath Y hc) (μ := P) (p := (2:ℝ≥0∞)) (by norm_num)).mp (le_antisymm hn bot_le)
  filter_upwards [hzpath] with ω hω
  intro t
  exact congrArg (fun f : C(ClosedTime T,ℝ) => f t) hω

/-- Full proof of A intersect M2={0}: actual total variation, its stopping
 times, uniform continuity of the stopped paths, square-sum DCT, optional
 sampling, Doob, and removal of the stopping. T=0 and T=infinity are included. -/
theorem continuous_bv_martingale_zero_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (h2 : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = 0 := by
  have hT : 0 ≤ T := Fact.out
  by_cases hpos : 0 < T
  swap
  · have hTeq : T = 0 := le_antisymm (not_lt.mp hpos) hT
    have he (t : ClosedTime T) : t = ⊥ := by
      apply Subtype.ext
      exact le_antisymm (t.property.2.trans_eq hTeq) t.property.1
    filter_upwards [hz] with ω hω
    intro t
    simpa only [he t,Pi.zero_apply] using hω
  let τ := fun k : ℕ => variationStop X (k:ℝ)
  have hτ (k) := variation_stop_stopping F hF X hm hc hb (k:ℝ)
  have hzt (k) : (fun ω => X (τ k ω) ω) =ᵐ[P] 0 :=
    bv_martingale_stopped_zero P hpos F hF hle X hm h2 hc hb hmart hz (Nat.cast_nonneg k)
  have hzero (k) : ∀ᵐ ω ∂P, ∀ t, X (min t (τ k ω)) ω = 0 := by
    have hmstop (t : ClosedTime T) : Measurable[m] (fun ω => X (min t (τ k ω)) ω) := by
      have ht (s : ClosedTime T) : MeasurableSet[F s] {ω : Ω | t ≤ s} := by
        by_cases h : t ≤ s <;> simp [h]
      have hmin := (written_stopping_min_max F (fun _ => t) (τ k) ht (hτ k)).1
      have h := stopped_value_measurable_right_continuous m hT F hF hle
        (fun ω => min t (τ k ω)) hmin X hm (fun ω t => (hc ω).continuousAt.continuousWithinAt)
      exact h.mono (fun A hA => hA.1) le_rfl
    apply continuous_zero_marginals_doob P _ hmstop (fun ω => (hc ω).comp (continuous_id.min continuous_const))
    intro t
    have h := stopped_value_conditional P F hF hle X hm (fun t => (h2 t).integrable (by norm_num)) hc hmart
      (τ k) (hτ k) t
    have hce := condExp_congr_ae (m := F t) (hzt k)
    simpa only [condExp_zero] using h.symm.trans hce
  filter_upwards [ae_all_iff.mpr hzero] with ω hω
  obtain ⟨K,hK⟩ := eventually_atTop.mp (variation_stop_eventually_terminal X hb ω)
  intro t
  have h := hω K t
  simpa only [τ,hK K le_rfl,min_top_right] using h

/-- The printed A assumption (difference of increasing finite-valued paths)
 implies the bounded-variation hypothesis used above. -/
theorem increasing_difference_boundedVariation {ι : Type*} [LinearOrder ι] [BoundedOrder ι]
    (A B : ι → ℝ) (hA : Monotone A) (hB : Monotone B) :
    BoundedVariationOn (fun t => A t-B t) univ := by
  have hAv : BoundedVariationOn A univ := by
    have h := hA.monotoneOn univ |>.eVariationOn_eq (mem_univ ⊥) (mem_univ ⊤)
    simp only [Icc_bot_top,univ_inter] at h
    exact h.trans_ne ENNReal.ofReal_ne_top
  have hBv : BoundedVariationOn B univ := by
    have h := hB.monotoneOn univ |>.eVariationOn_eq (mem_univ ⊥) (mem_univ ⊤)
    simp only [Icc_bot_top,univ_inter] at h
    exact h.trans_ne ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAv,hBv⟩)
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n,u,hu,hs⟩
  calc
    _ ≤ (∑ j ∈ Finset.range n, edist (A (u (j+1))) (A (u j))) +
        ∑ j ∈ Finset.range n, edist (B (u (j+1))) (B (u j)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j hj
      simp only [edist_dist,Real.dist_eq]
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h := abs_sub_le (A (u (j+1))-A (u j)) 0 (B (u (j+1))-B (u j))
      simpa only [sub_zero,abs_neg,zero_sub,show A (u (j+1))-A (u j)-(B (u (j+1))-B (u j)) =
        (A (u (j+1))-B (u (j+1)))-(A (u j)-B (u j)) by ring] using h
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hs) (eVariationOn.sum_le hu hs)

/-- Connect the actual decomposition in A to the full martingale argument. -/
theorem A_inter_M2_zero_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (h2 : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hA : ∀ ω, ∃ A B : ClosedTime T → ℝ, Monotone A ∧ Monotone B ∧ ∀ t, X t ω = A t-B t)
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = 0 := by
  apply continuous_bv_martingale_zero_written P F hF hle X hm h2 hc _ hmart hz
  intro ω
  obtain ⟨A,B,hA,hB,hX⟩ := hA ω
  simpa only [hX] using increasing_difference_boundedVariation A B hA hB

end Asakura.FullAudit
