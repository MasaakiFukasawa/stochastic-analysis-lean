import Chapter4FinitePathLift
import Chapter4PathRestriction
import Chapter4PicardDifferenceBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem finite_picard_prefix_difference
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (hCc : ∀ w t,t<⊤ → ContinuousAt (fun s => C s w) t)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (L : ℝ) (hL : 0≤L) (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y,(μ x-μ y)^2+(σ x-σ y)^2≤L*(x-y)^2)
    (ξ : Ω → ℝ)
    (Y₁ Y₂ V₁ V₂ : Ω → C(Icc (0:ℝ) R,ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (ha₁ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₁ w r))
    (ha₂ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₂ w r))
    (hv₁ : Measurable[m] V₁) (hv₂ : Measurable[m] V₂)
    (N₁ N₂ : ClosedTime T → Ω → ℝ)
    (hn₁ : LocalMProcessWitness P F N₁) (hn₂ : LocalMProcessWitness P F N₂)
    (hI₁ : ItoCovarianceFormula P F W
      (fun z => σ (Y₁ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N₁)
    (hI₂ : ItoCovarianceFormula P F W
      (fun z => σ (Y₂ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N₂)
    (he₁ : ∀ᵐ w ∂P,∀ r,V₁ w r=ξ w+(∫ s in 0..r.val,μ (Y₁ w (projIcc 0 R hR s)))+N₁ (realTimeClamp r.val) w)
    (he₂ : ∀ᵐ w ∂P,∀ r,V₂ w r=ξ w+(∫ s in 0..r.val,μ (Y₂ w (projIcc 0 R hR s)))+N₂ (realTimeClamp r.val) w)
    (d : ℝ) (hd : d∈Icc 0 R) :
    (∫ w,‖prefixPath hR (V₁ w-V₂ w) d‖^2 ∂P)≤
      ((2*R+8)*L)*(∫ r in 0..d,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P)) := by
  change 0≤d ∧ d≤R at hd
  letI : MeasurableSpace Ω := m
  let U₁ := fun t w => Y₁ w (finitePrefixTime (T := T) R hR t)
  let U₂ := fun t w => Y₂ w (finitePrefixTime (T := T) R hR t)
  have hU₁ := finite_path_lift_regular F hF R hR hRT.le Y₁ ha₁
  have hU₂ := finite_path_lift_regular F hF R hR hRT.le Y₂ ha₂
  have hdT : (d:EReal)<T := (EReal.coe_le_coe hd.2).trans_lt hRT
  let Z := fun t w => N₁ t w-N₂ t w
  have hZ : LocalMProcessWitness P F Z := by
    simpa only [neg_one_mul,neg_add_eq_sub] using (hn₂.smul P F (-1)).add P F hF hle hn₁
  have hzc := open_path_stopped_continuous Z (hZ.path P F) d hd.1 hdT
  let z := finiteRealPath Z d hzc
  let D := fun w => restrictRealPath hd.2 (V₁ w-V₂ w)-z w
  have hDm : Measurable[m] D :=
    (restrict_real_path_measurable hd.2 _ (hv₁.sub hv₂)).sub
      (finite_real_path_measurable F hle Z d hdT hzc (hZ.adapted P F))
  have hpoint (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (w : Ω) (r : ℝ) (hr : r∈Icc 0 d) :
      Y w (finitePrefixTime (T := T) R hR (realTimeClamp r))=
        restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r) := by
    rw [projIcc_of_mem hd.1 hr]
    dsimp only [restrictRealPath,ContinuousMap.coe_mk]
    congr 1
    apply Subtype.ext
    exact finite_prefix_time_of_real R r hR ⟨hr.1,hr.2.trans hd.2⟩ hRT.le
  have hpoint' (Y : Ω → C(Icc (0:ℝ) R,ℝ)) (w : Ω) (r : ℝ) (hr : r∈Icc 0 d) :
      restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r)=Y w (projIcc 0 R hR r) := by
    rw [projIcc_of_mem hd.1 hr,projIcc_of_mem hR ⟨hr.1,hr.2.trans hd.2⟩]
    rfl
  have hD : ∀ᵐ w ∂P,∀ t,D w t=∫ r in 0..t.val,
      (μ (restrictRealPath hd.2 (Y₁ w) (projIcc 0 d hd.1 r))-
       μ (restrictRealPath hd.2 (Y₂ w) (projIcc 0 d hd.1 r))) := by
    filter_upwards [he₁,he₂] with w h₁ h₂
    intro t
    have hμ₁ : Continuous (fun r => μ (Y₁ w (projIcc 0 R hR r))) := hμ.comp ((Y₁ w).continuous.comp continuous_projIcc)
    have hμ₂ : Continuous (fun r => μ (Y₂ w (projIcc 0 R hR r))) := hμ.comp ((Y₂ w).continuous.comp continuous_projIcc)
    have hi : (∫ r in 0..t.val,(μ (restrictRealPath hd.2 (Y₁ w) (projIcc 0 d hd.1 r))-
        μ (restrictRealPath hd.2 (Y₂ w) (projIcc 0 d hd.1 r))))=
      (∫ r in 0..t.val,μ (Y₁ w (projIcc 0 R hR r)))-(∫ r in 0..t.val,μ (Y₂ w (projIcc 0 R hR r))) := by
      rw [← intervalIntegral.integral_sub (hμ₁.intervalIntegrable _ _) (hμ₂.intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r∈Icc 0 d := Icc_subset_Icc_right t.property.2 (by simpa [uIcc_of_le t.property.1] using hr)
      dsimp only
      rw [hpoint' Y₁ w r hr',hpoint' Y₂ w r hr']
    rw [hi]
    change (V₁ w ⟨t.val,t.property.1,t.property.2.trans hd.2⟩-V₂ w ⟨t.val,t.property.1,t.property.2.trans hd.2⟩)-
      (N₁ (realTimeClamp t.val) w-N₂ (realTimeClamp t.val) w)=_
    rw [h₁,h₂]
    ring
  obtain ⟨hzc',hi,hb⟩ := sde_picard_difference_bound P hT F hF hle hnull W C U₁ U₂ N₁ N₂
    hW hC hCm hCc hclock (fun t _ => hU₁.1 t) (fun t _ => hU₂.1 t)
    (fun w t _ => (hU₁.2 w).continuousAt) (fun w t _ => (hU₂.2 w).continuousAt)
    L hL μ σ hμ hσ hLip hn₁ hn₂ hI₁ hI₂ d hd.1 hdT
    (fun w => restrictRealPath hd.2 (Y₁ w)) (fun w => restrictRealPath hd.2 (Y₂ w))
    (restrict_real_path_measurable hd.2 Y₁ hm₁) (restrict_real_path_measurable hd.2 Y₂ hm₂)
    (restrict_real_path_memLp P hd.2 Y₁ hm₁ hi₁) (restrict_real_path_memLp P hd.2 Y₂ hm₂ hi₂)
    (hpoint Y₁) (hpoint Y₂) D hDm.aestronglyMeasurable hD
  have hepath w : D w+finiteRealPath (fun t w => N₁ t w-N₂ t w) d hzc' w=
      restrictRealPath hd.2 (V₁ w-V₂ w) := by
    ext r
    dsimp only [D,z,Z,finiteRealPath,restrictRealPath,ContinuousMap.coe_mk,ContinuousMap.add_apply,ContinuousMap.sub_apply]
    ring
  simp_rw [hepath,restriction_eq_prefix_norm hd.1 hd.2] at hb
  have hint : (∫ r in 0..d,(∫ w,‖prefixPath hd.1 (restrictRealPath hd.2 (Y₁ w)-restrictRealPath hd.2 (Y₂ w)) r‖^2 ∂P))=
      ∫ r in 0..d,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 d := by simpa [uIcc_of_le hd.1] using hr
    apply integral_congr_ae
    exact .of_forall (fun w => by dsimp only; rw [← restrict_real_path_sub,restricted_prefix_norm hd.1 hd.2 _ r hr'])
  rw [hint] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hd.2]) hL)
    (intervalIntegral.integral_nonneg_of_forall hd.1 (fun r => integral_nonneg (fun w => sq_nonneg _))))

end Asakura.Chapter4
