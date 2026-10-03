import Chapter4VectorFiniteLift
import Chapter4VectorPathRestriction
import Chapter4VectorPicardBound

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem finite_picard_prefix_difference
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
    (ξ : Ω → Fin dim → ℝ)
    (Y₁ Y₂ V₁ V₂ : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (ha₁ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₁ w r))
    (ha₂ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₂ w r))
    (hv₁ : Measurable[m] V₁) (hv₂ : Measurable[m] V₂)
    (N₁ N₂ : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn₁ : ∀ i j,LocalMProcessWitness P F (N₁ i j))
    (hn₂ : ∀ i j,LocalMProcessWitness P F (N₂ i j))
    (hI₁ : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y₁ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N₁ i j))
    (hI₂ : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y₂ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N₂ i j))
    (he₁ : ∀ᵐ w ∂P,∀ r i,V₁ w r i=ξ w i+(∫ s in 0..r.val,μ i (Y₁ w (projIcc 0 R hR s)))+∑ j,N₁ i j (realTimeClamp r.val) w)
    (he₂ : ∀ᵐ w ∂P,∀ r i,V₂ w r i=ξ w i+(∫ s in 0..r.val,μ i (Y₂ w (projIcc 0 R hR s)))+∑ j,N₂ i j (realTimeClamp r.val) w)
    (d : ℝ) (hd : d∈Icc 0 R) :
    (∫ w,‖prefixPath hR (V₁ w-V₂ w) d‖^2 ∂P)≤
      ((dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L)*(∫ r in 0..d,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P)) := by
  change 0≤d ∧ d≤R at hd
  letI : MeasurableSpace Ω := m
  let U₁ := fun t w => Y₁ w (finitePrefixTime (T := T) R hR t)
  let U₂ := fun t w => Y₂ w (finitePrefixTime (T := T) R hR t)
  have hU₁ := finite_path_lift_regular F hF R hR hRT.le Y₁ ha₁
  have hU₂ := finite_path_lift_regular F hF R hR hRT.le Y₂ ha₂
  have hdT : (d:EReal)<T := (EReal.coe_le_coe hd.2).trans_lt hRT
  let Z := fun i j t w => N₁ i j t w-N₂ i j t w
  let H := fun i j t w => σ i j (U₁ t w)-σ i j (U₂ t w)
  have hZ i j : LocalMProcessWitness P F (Z i j) := by
    simpa only [neg_one_mul,neg_add_eq_sub] using ((hn₂ i j).smul P F (-1)).add P F hF hle (hn₁ i j)
  have hZI i j : ItoCovarianceFormula P F (W j) (fun z => H i j (realTimeClamp z.2) z.1) (Z i j) := by
    simpa only [neg_one_mul,neg_add_eq_sub] using
      (hI₂ i j).add_smul P F hF hle (W j) (N₂ i j) (N₁ i j) _ _ (hI₁ i j) (-1)
  have hHa i j t (_ht : t<⊤) : Measurable[F t] (H i j t) :=
    ((hσ i j).measurable.comp (hU₁.1 t)).sub ((hσ i j).measurable.comp (hU₂.1 t))
  have hHc i j w t (_ht : t<⊤) : ContinuousAt (fun s => H i j s w) t :=
    ((hσ i j).continuousAt.comp (hU₁.2 w).continuousAt).sub
      ((hσ i j).continuousAt.comp (hU₂.2 w).continuousAt)
  have hpoint (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (w : Ω) (r : ℝ) (hr : r∈Icc 0 d) :
      Y w (finitePrefixTime (T := T) R hR (realTimeClamp r))=
        restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r) := by
    rw [projIcc_of_mem hd.1 hr]
    dsimp only [restrictRealPath,ContinuousMap.coe_mk]
    congr 1
    apply Subtype.ext
    exact finite_prefix_time_of_real R r hR ⟨hr.1,hr.2.trans hd.2⟩ hRT.le
  have hpoint' (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (w : Ω) (r : ℝ) (hr : r∈Icc 0 d) :
      restrictRealPath hd.2 (Y w) (projIcc 0 d hd.1 r)=Y w (projIcc 0 R hR r) := by
    rw [projIcc_of_mem hd.1 hr,projIcc_of_mem hR ⟨hr.1,hr.2.trans hd.2⟩]
    rfl
  have he : ∀ᵐ w ∂P,∀ (t : Icc (0:ℝ) d) i,restrictRealPath hd.2 (V₁ w-V₂ w) t i=
      (∫ r in 0..t.val,(μ i (restrictRealPath hd.2 (Y₁ w) (projIcc 0 d hd.1 r))-
        μ i (restrictRealPath hd.2 (Y₂ w) (projIcc 0 d hd.1 r))))+∑ j,Z i j (realTimeClamp t.val) w := by
    filter_upwards [he₁,he₂] with w h₁ h₂
    intro t i
    have hc₁ : Continuous (fun r => μ i (Y₁ w (projIcc 0 R hR r))) := (hμ i).comp ((Y₁ w).continuous.comp continuous_projIcc)
    have hc₂ : Continuous (fun r => μ i (Y₂ w (projIcc 0 R hR r))) := (hμ i).comp ((Y₂ w).continuous.comp continuous_projIcc)
    have hi : (∫ r in 0..t.val,(μ i (restrictRealPath hd.2 (Y₁ w) (projIcc 0 d hd.1 r))-
        μ i (restrictRealPath hd.2 (Y₂ w) (projIcc 0 d hd.1 r))))=
        (∫ r in 0..t.val,μ i (Y₁ w (projIcc 0 R hR r)))-(∫ r in 0..t.val,μ i (Y₂ w (projIcc 0 R hR r))) := by
      rw [← intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r∈Icc 0 d := Icc_subset_Icc_right t.property.2 (by simpa [uIcc_of_le t.property.1] using hr)
      dsimp only
      rw [hpoint' Y₁ w r hr',hpoint' Y₂ w r hr']
    rw [hi]
    change V₁ w ⟨t.val,t.property.1,t.property.2.trans hd.2⟩ i-V₂ w ⟨t.val,t.property.1,t.property.2.trans hd.2⟩ i=_
    rw [h₁,h₂]
    simp only [Z,Finset.sum_sub_distrib]
    ring
  obtain ⟨_,hb⟩ := vector_picard_difference_bound P hT F hF hle hnull W C hW hC hclock
    d L hd.1 hdT hL μ σ hμ hσ hμLip hσLip
    (fun w => restrictRealPath hd.2 (Y₁ w)) (fun w => restrictRealPath hd.2 (Y₂ w))
    (fun w => restrictRealPath hd.2 (V₁ w-V₂ w))
    (restrict_real_path_measurable hd.2 Y₁ hm₁) (restrict_real_path_measurable hd.2 Y₂ hm₂)
    (restrict_real_path_measurable hd.2 _ (hv₁.sub hv₂))
    (restrict_real_path_memLp P hd.2 Y₁ hm₁ hi₁) (restrict_real_path_memLp P hd.2 Y₂ hm₂ hi₂)
    H Z hHa hHc hZ hZI
    (fun i j w r hr => by dsimp only [H,U₁,U₂]; rw [hpoint Y₁ w r hr,hpoint Y₂ w r hr]) he
  simp_rw [restriction_eq_prefix_norm hd.1 hd.2] at hb
  have hint : (∫ r in 0..d,(∫ w,‖prefixPath hd.1 (restrictRealPath hd.2 (Y₁ w)-restrictRealPath hd.2 (Y₂ w)) r‖^2 ∂P))=
      ∫ r in 0..d,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 d := by simpa [uIcc_of_le hd.1] using hr
    apply integral_congr_ae
    exact .of_forall (fun w => by dsimp only; rw [← restrict_real_path_sub,restricted_prefix_norm hd.1 hd.2 _ r hr'])
  rw [hint] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (intervalIntegral.integral_nonneg_of_forall hd.1 (fun r => integral_nonneg (fun w => sq_nonneg _)))
  apply mul_le_mul_of_nonneg_right _ hL
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg dim)
  linarith only [hd.2]

end Asakura.Chapter4.Vector
