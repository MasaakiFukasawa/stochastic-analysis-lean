import Chapter4FinitePicardDifference
import Chapter4PrefixIntegralBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Continuity in L² of the actual Picard map, derived from the prefix
estimate for its constructed stochastic integrals. -/
theorem finite_picard_L2_difference
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
    (hvi₁ : MemLp V₁ 2 P) (hvi₂ : MemLp V₂ 2 P) :
    eLpNorm (fun w => V₁ w-V₂ w) 2 P≤
      ENNReal.ofReal (Real.sqrt (((2*R+8)*L)*R))*eLpNorm (fun w => Y₁ w-Y₂ w) 2 P := by
  letI : MeasurableSpace Ω := m
  have hb := finite_picard_prefix_difference P hT F hF hle hnull W C hW hC hCm hCc hclock
    R hR hRT L hL μ σ hμ hσ hLip ξ Y₁ Y₂ V₁ V₂ hm₁ hm₂ hi₁ hi₂ ha₁ ha₂ hv₁ hv₂
    N₁ N₂ hn₁ hn₂ hI₁ hI₂ he₁ he₂ R ⟨hR,le_rfl⟩
  simp only [prefix_path_endpoint] at hb
  have hc : 0≤(2*R+8)*L := by positivity
  have hp := prefix_integral_le_full_moment P R hR (fun w => Y₁ w-Y₂ w) (hm₁.sub hm₂) (hi₁.sub hi₂)
  apply path_eLpNorm_bound_of_squared_moment P _ _ (hvi₁.sub hvi₂) (hi₁.sub hi₂) _ (mul_nonneg hc hR)
  exact hb.trans (by simpa only [Pi.sub_apply,mul_assoc] using mul_le_mul_of_nonneg_left hp hc)

end Asakura.Chapter4
