import Chapter10KyleFiniteGainSufficiency
import Chapter4ItoPrefixCongruence

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the actual filter and price equations after identifying their
noise integrals. The value may vary with time. All continuity is local. -/
theorem kyle_coupled_equations (a p v k l β n : ℝ → ℝ) (p0 R : ℝ) (hR : 0≤R)
    (ha : ContinuousOn a (Icc 0 R)) (hp : ContinuousOn p (Icc 0 R))
    (hv : ContinuousOn v (Icc 0 R)) (hk : ContinuousOn k (Icc 0 R))
    (hl : ContinuousOn l (Icc 0 R)) (hβ : ContinuousOn β (Icc 0 R))
    (hg : ∀ t∈Icc 0 R,k t=l t)
    (heqa : ∀ t∈Icc 0 R,a t=p0+(∫ s in 0..t,k s*β s*(v s-a s))+n t)
    (heqp : ∀ t∈Icc 0 R,p t=p0+(∫ s in 0..t,l s*β s*(v s-p s))+n t) :
    ∀ t∈Icc 0 R,a t=p t := by
  apply kyle_finite_gain_sufficiency a p (fun t => p t-p0) l β p0 R hR ha hp hl hβ
  · intro t ht; ring
  · intro t ht
    have hsub : (Icc 0 t)⊆Icc 0 R := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    have hi₁ := (((hl.mul hβ).mul (hv.sub hp)).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hi₂ := (((hl.mul hβ).mul (hp.sub ha)).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    change IntervalIntegrable (fun s => l s*β s*(v s-p s)) volume 0 t at hi₁
    change IntervalIntegrable (fun s => l s*β s*(p s-a s)) volume 0 t at hi₂
    have he : (∫ s in 0..t,k s*β s*(v s-a s))=
        (∫ s in 0..t,l s*β s*(v s-p s))+(∫ s in 0..t,l s*β s*(p s-a s)) := by
      rw [←intervalIntegral.integral_add hi₁ hi₂]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      dsimp only
      rw [hg s (hsub hs)]
      ring
    rw [heqa t ht,heqp t ht,he]
    ring

/-- Actual stochastic filter and candidate price equations with equal gains
have equal solutions. Equality of the stochastic integrals is derived from
Ito's construction on the finite interval, not postulated. -/
theorem kyle_actual_gain_sufficiency {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (W C N M H₁ H₂ : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w r,0≤r → C (realTimeClamp r) w=r)
    (hN : LocalMProcessWitness P F N) (hM : LocalMProcessWitness P F M)
    (hNI : ItoCovarianceFormula P F W (fun z => H₁ (realTimeClamp z.2) z.1) N)
    (hMI : ItoCovarianceFormula P F W (fun z => H₂ (realTimeClamp z.2) z.1) M)
    (ha₁ : ∀ t,t<⊤ → Measurable[F t] (H₁ t))
    (ha₂ : ∀ t,t<⊤ → Measurable[F t] (H₂ t))
    (hc₁ : ∀ w t,t<⊤ → ContinuousAt (fun s => H₁ s w) t)
    (hc₂ : ∀ w t,t<⊤ → ContinuousAt (fun s => H₂ s w) t)
    (a p v : Ω → ℝ → ℝ) (k l β : ℝ → ℝ) (σ p0 R : ℝ) (hR : 0≤R)
    (ha : ∀ w,ContinuousOn (a w) (Icc 0 R))
    (hp : ∀ w,ContinuousOn (p w) (Icc 0 R))
    (hv : ∀ w,ContinuousOn (v w) (Icc 0 R))
    (hk : ContinuousOn k (Icc 0 R)) (hl : ContinuousOn l (Icc 0 R))
    (hβ : ContinuousOn β (Icc 0 R)) (hg : ∀ t∈Icc 0 R,k t=l t)
    (hH₁ : ∀ w t,t∈Icc 0 R → H₁ (realTimeClamp t) w=k t*σ)
    (hH₂ : ∀ w t,t∈Icc 0 R → H₂ (realTimeClamp t) w=l t*σ)
    (heqa : ∀ᵐ w ∂P,∀ t∈Icc 0 R,
      a w t=p0+(∫ s in 0..t,k s*β s*(v w s-a w s))+N (realTimeClamp t) w)
    (heqp : ∀ᵐ w ∂P,∀ t∈Icc 0 R,
      p w t=p0+(∫ s in 0..t,l s*β s*(v w s-p w s))+M (realTimeClamp t) w) :
    ∀ᵐ w ∂P,∀ t∈Icc 0 R,a w t=p w t := by
  have he := brownian_ito_prefix_congr P (by simp : (0:EReal)<⊤) F hF hle hnull
    W C hW hC (fun w r hr _ => hclock w r hr) H₁ H₂ N M ha₁ ha₂ hc₁ hc₂ hN hM hNI hMI
    R hR (EReal.coe_lt_top R) (Filter.Eventually.of_forall (fun w t ht => by
      rw [hH₁ w t ht,hH₂ w t ht,hg t ht]))
  filter_upwards [he,heqa,heqp] with w hw hwa hwp
  exact kyle_coupled_equations (a w) (p w) (v w) k l β
    (fun t => M (realTimeClamp t) w) p0 R hR (ha w) (hp w) (hv w) hk hl hβ hg
    (fun t ht => by rw [hwa t ht,hw t ht]) hwp

end Asakura.Chapter10
