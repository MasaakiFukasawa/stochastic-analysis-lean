import Chapter4VectorDriftPath
import Chapter4VectorNoisePath
import Chapter4FiniteSumPathMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

lemma one_coefficient_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {dim : ℕ}
    (R L : ℝ) (hR : 0≤R) (hL : 0≤L)
    (b : (Fin dim → ℝ) → ℝ) (hb : Continuous b)
    (hLip : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) :
    MemLp (fun z : Ω × ℝ => b (Y z.1 (projIcc 0 R hR z.2))) 2
      (P.prod (volume.restrict (Ioc (0:ℝ) R))) := by
  exact (coefficient_path_memLp P R L hR hL b (fun _ => 0) hb continuous_const
    (by simpa only [sub_self,zero_pow (by decide : (2:ℕ)≠0),add_zero] using hLip) Y hm hi).1

/-- The full finite-dimensional Picard map, with one constructed Ito integral
for each matrix entry. It preserves adapted L² continuous paths, including
zero-dimensional coordinate sets. -/
theorem finite_picard_image
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hYm : Measurable[m] Y) (hYi : MemLp Y 2 P)
    (hYa : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y w r)) :
    ∃ (V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      (∀ i j,LocalMProcessWitness P F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j)
        (fun z => σ i j (Y z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N i j)) ∧
      ∀ w r i,V w r i=ξ w i+(∫ s in 0..r.val,μ i (Y w (projIcc 0 R hR s)))+∑ j,N i j (realTimeClamp r.val) w := by
  classical
  letI : MeasurableSpace Ω := m
  have hD i := drift_path_constructed P F hF hle R hR Y hYm hYa (μ i) (hμ i)
    (one_coefficient_memLp P R L hR hL (μ i) (hμ i) (hμLip i) Y hYm hYi)
  choose D hDm hDi hDa hDr hDb using hD
  have hN i j := noise_path_constructed P hT F hF hle hnull (W j) (C j) (hW j) (hC j) (hclock j)
    R hR hRT Y hYa (σ i j) (hσ i j)
    (one_coefficient_memLp P R L hR hL (σ i j) (hσ i j) (hσLip i j) Y hYm hYi)
  choose N Z hNloc hNI hZm hZi hZa hZr hZb using hN
  let B := fun i w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w i)
  have hBm i : Measurable[m] (B i) := ContinuousMap.measurable_iff_eval.mpr (fun _ =>
    (measurable_pi_apply i).comp (hξ.mono (hle _) le_rfl))
  have hBi i : MemLp (B i) 2 P := by
    apply hξi.of_le_mul (c := 1) (hBm i).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [one_mul]
    exact ((ContinuousMap.norm_le _ (norm_nonneg (ξ w i))).2 (fun _ => le_rfl)).trans (norm_le_pi_norm (ξ w) i)
  let Vc := fun i w => B i w+D i w+∑ j,Z i j w
  have hVcm i : Measurable[m] (Vc i) :=
    ((hBm i).add (hDm i)).add (Finset.measurable_sum Finset.univ (fun j _ => hZm i j))
  have hVci i : MemLp (Vc i) 2 P := by
    have hs : MemLp (fun w => ∑ j,Z i j w) 2 P :=
      (finite_sum_path_moment P (Z i) (hZi i)).1
    have hbd : MemLp (fun w => B i w+D i w) 2 P :=
      MemLp.add (f := B i) (g := D i) (hBi i) (hDi i)
    exact MemLp.add (f := fun w => B i w+D i w) (g := fun w => ∑ j,Z i j w) hbd hs
  refine ⟨fun w => bundleRealPaths (fun i => Vc i w),N,
    bundle_path_measurable Vc hVcm,bundle_path_memLp P Vc hVcm hVci,?_,hNloc,hNI,?_⟩
  · intro r
    letI : MeasurableSpace Ω := F (realTimeClamp r.val)
    apply measurable_pi_iff.mpr
    intro i
    have hξa : Measurable[F (realTimeClamp r.val)] (fun w => ξ w i) :=
      (measurable_pi_apply i).comp (hξ.mono (hF bot_le) le_rfl)
    simpa only [bundleRealPaths,Vc,B,ContinuousMap.coe_mk,ContinuousMap.add_apply,
      ContinuousMap.const_apply,ContinuousMap.sum_apply,Pi.add_def] using
      (hξa.add (hDa i r)).add (Finset.measurable_sum Finset.univ (fun j _ => hZa i j r))
  · intro w r i
    simp only [bundleRealPaths,Vc,B,ContinuousMap.coe_mk,ContinuousMap.add_apply,
      ContinuousMap.const_apply,ContinuousMap.sum_apply,hDr,hZr]

end Asakura.Chapter4.Vector
