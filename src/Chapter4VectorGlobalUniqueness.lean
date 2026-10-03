import Chapter4VectorGlobalRestriction
import Chapter4VectorFiniteUniquenessComplete

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- All-time pathwise uniqueness, with moment assumptions only on the
initial value. The countable exhaustion gives one common exceptional set. -/
theorem vector_sde_global_unique
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (L : ℝ) (hL : 0≤L)
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξm : Measurable[m] ξ) (hξi : MemLp ξ 2 P)
    (X₁ X₂ : ClosedTime T → Ω → Fin dim → ℝ)
    (ha₁ : ∀ t,t<⊤ → Measurable[F t] (X₁ t)) (ha₂ : ∀ t,t<⊤ → Measurable[F t] (X₂ t))
    (hc₁ : ∀ w t,t<⊤ → ContinuousAt (fun s => X₁ s w) t)
    (hc₂ : ∀ w t,t<⊤ → ContinuousAt (fun s => X₂ s w) t)
    (N₁ N₂ : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn₁ : ∀ i j,LocalMProcessWitness P F (N₁ i j))
    (hn₂ : ∀ i j,LocalMProcessWitness P F (N₂ i j))
    (hI₁ : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X₁ (realTimeClamp z.2) z.1)) (N₁ i j))
    (hI₂ : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X₂ (realTimeClamp z.2) z.1)) (N₂ i j))
    (he₁ : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X₁ (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X₁ (realTimeClamp s) w))+∑ j,N₁ i j (realTimeClamp r) w)
    (he₂ : ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
      X₂ (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X₂ (realTimeClamp s) w))+∑ j,N₂ i j (realTimeClamp r) w) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → X₁ t w=X₂ t w := by
  letI : MeasurableSpace Ω := m
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hh n : realVectorPath X₁ hc₁ (c n) (hcT n)=ᵐ[P] realVectorPath X₂ hc₂ (c n) (hcT n) := by
    obtain ⟨J₁,hJ₁,hJI₁,hJe₁⟩ := global_sde_finite_restriction P hT F hF hle hnull W C hW hC hclock
      μ σ hσ ξ X₁ ha₁ hc₁ N₁ hn₁ hI₁ he₁ (c n) (hc n).le (hcT n)
    obtain ⟨J₂,hJ₂,hJI₂,hJe₂⟩ := global_sde_finite_restriction P hT F hF hle hnull W C hW hC hclock
      μ σ hσ ξ X₂ ha₂ hc₂ N₂ hn₂ hI₂ he₂ (c n) (hc n).le (hcT n)
    have hYa₁ r : Measurable[F (realTimeClamp r.val)] (fun w => realVectorPath X₁ hc₁ (c n) (hcT n) w r) :=
      ha₁ _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt (hcT n)))
    have hYa₂ r : Measurable[F (realTimeClamp r.val)] (fun w => realVectorPath X₂ hc₂ (c n) (hcT n) w r) :=
      ha₂ _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt (hcT n)))
    exact vector_sde_finite_unique P hT F hF hle hnull W C hW hC hclock (c n) (hc n).le (hcT n) L hL
      μ σ hμ hσ hμLip hσLip ξ hξm hξi _ _
      (ContinuousMap.measurable_iff_eval.mpr (fun r => (hYa₁ r).mono (hle _) le_rfl))
      (ContinuousMap.measurable_iff_eval.mpr (fun r => (hYa₂ r).mono (hle _) le_rfl))
      hYa₁ hYa₂ J₁ J₂ hJ₁ hJ₂ hJI₁ hJI₂ hJe₁ hJe₂
  filter_upwards [ae_all_iff.mpr hh] with w hw
  intro t ht
  obtain ⟨n,hn⟩ := hcc t ht
  obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t ht
  have hrn : r≤c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
    exact (EReal.coe_lt_coe_iff.mp hn).le
  exact congrArg (fun V : C(Icc (0:ℝ) (c n),Fin dim → ℝ) => V ⟨r,hr,hrn⟩) (hw n)

end Asakura.Chapter4.Vector
