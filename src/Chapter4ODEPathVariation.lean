import Chapter4FlowDerivative
import Chapter4FinitePathLift
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma ode_finite_lipschitz (R : ℝ) (hR : 0≤R) (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hd : ∀ r∈Ioo 0 R,HasDerivAt f (g r) r) :
    ∃ C : ℝ≥0,LipschitzOnWith C f (Icc 0 R) := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  let C : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hi a b (ha : a∈Icc 0 R) (hb : b∈Icc 0 R) (hab : a≤b) :
      ‖f b-f a‖≤(C:ℝ)*(b-a) := by
    have hsub : Icc a b ⊆ Icc 0 R := fun _ hx => ⟨ha.1.trans hx.1,hx.2.trans hb.2⟩
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hf.mono hsub)
      (fun x hx => hd x ⟨ha.1.trans_lt hx.1,hx.2.trans_le hb.2⟩)
      ((hg.mono hsub).intervalIntegrable_of_Icc hab)
    rw [←he]
    have he' := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := (C:ℝ)) (f := g) (fun x hx => (hB x (hsub ⟨(uIoc_of_le hab ▸ hx).1.le,
        (uIoc_of_le hab ▸ hx).2⟩)).trans (le_max_left B 0))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using he'
  refine ⟨C,lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  intro a ha b hb
  rcases le_total a b with hab | hba
  · simpa only [Real.dist_eq,Real.norm_eq_abs,abs_sub_comm (f a) (f b),abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr hab)] using hi a b ha hb hab
  · simpa only [Real.dist_eq,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hba)] using hi b a hb ha hba

/-- A continuous adapted solution of an ordinary differential equation with
continuous pathwise right-hand side has locally bounded variation. The endpoint
zero only requires continuity, not a derivative of the artificially clamped path. -/
theorem ode_adapted_local_variation
    {Ω : Type*} {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (Y : ClosedTime T → Ω → ℝ) (G : ℝ → Ω → ℝ)
    (ha : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (hgc : ∀ w (R : ℝ),0≤R → (R:EReal)<T → ContinuousOn (fun r => G r w) (Icc 0 R))
    (hd : ∀ w (r : ℝ),0<r → (r:EReal)<T →
      HasDerivAt (fun s => Y (realTimeClamp s) w) (G r w) r) :
    AdaptedLocalVariationWitness F Y := by
  obtain ⟨c,hc0,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  refine ⟨fun n _ => realTimeClamp (c n),?_,fun _ => hct.monotone,
    fun n _ => hcut n,fun _ => hcc,?_⟩
  · intro n t
    by_cases h : realTimeClamp (T := T) (c n)≤t <;> simp [h]
  · intro n
    have hsa t : Measurable[F t] (fun w => Y (min (realTimeClamp (c n)) t) w) :=
      (ha _ ((min_le_left _ _).trans_lt (hcut n))).mono (hF (min_le_right _ _)) le_rfl
    have hsc := open_path_stopped_continuous Y hc (c n) (hc0 n).le (hcT n)
    have hb w : BoundedVariationOn (fun t => Y (min (realTimeClamp (c n)) t) w) univ := by
      have hyc : ContinuousOn (fun r : ℝ => Y (realTimeClamp r) w) (Icc 0 (c n)) := by
        intro r hr
        exact ((hc w _ (real_time_below r hr.1 ((EReal.coe_le_coe_iff.mpr hr.2).trans_lt (hcT n)))).comp
          real_time_clamp_continuous.continuousAt).continuousWithinAt
      obtain ⟨C,hC⟩ := ode_finite_lipschitz (c n) (hc0 n).le _ _ hyc (hgc w _ (hc0 n).le (hcT n))
        (fun r hr => hd w r hr.1 ((EReal.coe_lt_coe_iff.mpr hr.2).trans (hcT n)))
      have hq : Monotone (fun t : ClosedTime T => (finitePrefixTime (c n) (hc0 n).le t).val) :=
        finite_prefix_time_mono (c n) (hc0 n).le
      have hqv := (hq.monotoneOn univ).boundedVariationOn (C := c n)
        (fun t _ => (abs_of_nonneg (finitePrefixTime (c n) (hc0 n).le t).property.1).le.trans
          (finitePrefixTime (c n) (hc0 n).le t).property.2)
      have hb := hC.comp_boundedVariationOn (fun t _ => (finitePrefixTime (c n) (hc0 n).le t).property) hqv
      simpa only [Function.comp_def,finite_prefix_time_clamp (c n) (hc0 n).le (hcT n).le] using hb
    obtain ⟨U,V,hUa,hVa,hUc,hVc,hUm,hVm,he⟩ := adapted_continuous_jordan_decomposition F hF _ hsa hsc hb
    exact ⟨U,V,fun t => ⟨hUa t,hVa t⟩,fun w => ⟨hUm w,hVm w⟩,
      fun w t => ⟨(hUc w).continuousAt.continuousWithinAt,(hVc w).continuousAt.continuousWithinAt⟩,he⟩

end Asakura.Chapter4
