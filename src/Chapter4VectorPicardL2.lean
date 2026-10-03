import Chapter4VectorPrefixDifference
import Chapter4VectorPrefixIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Continuity in L² of the actual Picard map, derived from the prefix
estimate for its constructed stochastic integrals. -/
theorem finite_picard_L2_difference
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
    (hvi₁ : MemLp V₁ 2 P) (hvi₂ : MemLp V₂ 2 P) :
    eLpNorm (fun w => V₁ w-V₂ w) 2 P≤
      ENNReal.ofReal (Real.sqrt (((dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L)*R))*eLpNorm (fun w => Y₁ w-Y₂ w) 2 P := by
  letI : MeasurableSpace Ω := m
  have hb := finite_picard_prefix_difference P hT F hF hle hnull W C hW hC hclock
    R hR hRT L hL μ σ hμ hσ hμLip hσLip ξ Y₁ Y₂ V₁ V₂ hm₁ hm₂ hi₁ hi₂ ha₁ ha₂ hv₁ hv₂
    N₁ N₂ hn₁ hn₂ hI₁ hI₂ he₁ he₂ R ⟨hR,le_rfl⟩
  simp only [prefix_path_endpoint] at hb
  have hc : 0≤(dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L := by positivity
  have hp := prefix_integral_le_full_moment P R hR (fun w => Y₁ w-Y₂ w) (hm₁.sub hm₂) (hi₁.sub hi₂)
  apply path_eLpNorm_bound_of_squared_moment P _ _ (hvi₁.sub hvi₂) (hi₁.sub hi₂) _ (mul_nonneg hc hR)
  exact hb.trans (by simpa only [Pi.sub_apply,mul_assoc] using mul_le_mul_of_nonneg_left hp hc)

end Asakura.Chapter4.Vector
