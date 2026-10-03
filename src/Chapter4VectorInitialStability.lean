import Chapter4VectorPrefixDifference
import Chapter4VectorInitialSplit
import Chapter4VectorVolterraLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The initial-value stability estimate in the Markov proof, derived from
the two actual Ito equations and the already proved difference estimate. -/
theorem finite_sde_initial_stability
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
    (ξ₁ ξ₂ : Ω → Fin dim → ℝ) (hξm₁ : Measurable[m] ξ₁) (hξm₂ : Measurable[m] ξ₂)
    (hξi₁ : MemLp ξ₁ 2 P) (hξi₂ : MemLp ξ₂ 2 P)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (ha₁ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₁ w r))
    (ha₂ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₂ w r))
    (N₁ N₂ : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hn₁ : ∀ i j,LocalMProcessWitness P F (N₁ i j))
    (hn₂ : ∀ i j,LocalMProcessWitness P F (N₂ i j))
    (hI₁ : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y₁ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N₁ i j))
    (hI₂ : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (Y₂ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) (N₂ i j))
    (he₁ : ∀ᵐ w ∂P,∀ r i,Y₁ w r i=ξ₁ w i+(∫ s in 0..r.val,μ i (Y₁ w (projIcc 0 R hR s)))+∑ j,N₁ i j (realTimeClamp r.val) w)
    (he₂ : ∀ᵐ w ∂P,∀ r i,Y₂ w r i=ξ₂ w i+(∫ s in 0..r.val,μ i (Y₂ w (projIcc 0 R hR s)))+∑ j,N₂ i j (realTimeClamp r.val) w)
 :
    (∫ w,‖Y₁ w-Y₂ w‖^2 ∂P)≤
      (2*Real.exp ((2*((dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L)+1)*R))*(∫ w,‖ξ₁ w-ξ₂ w‖^2 ∂P) := by
  let J₁ := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ₁ w)
  let J₂ := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ₂ w)
  let V₁ := fun w => Y₁ w-J₁ w
  let V₂ := fun w => Y₂ w-J₂ w
  have hjm₁ : Measurable[m] J₁ := ContinuousMap.measurable_iff_eval.mpr (fun _ => hξm₁)
  have hjm₂ : Measurable[m] J₂ := ContinuousMap.measurable_iff_eval.mpr (fun _ => hξm₂)
  have hv₁ : Measurable[m] V₁ := hm₁.sub hjm₁
  have hv₂ : Measurable[m] V₂ := hm₂.sub hjm₂
  have hvrep₁ : ∀ᵐ w ∂P,∀ r i,V₁ w r i=(0:Fin dim → ℝ) i+
      (∫ s in 0..r.val,μ i (Y₁ w (projIcc 0 R hR s)))+∑ j,N₁ i j (realTimeClamp r.val) w := by
    filter_upwards [he₁] with w hw
    intro r i
    change Y₁ w r i-ξ₁ w i=0+_+_
    rw [hw]
    ring
  have hvrep₂ : ∀ᵐ w ∂P,∀ r i,V₂ w r i=(0:Fin dim → ℝ) i+
      (∫ s in 0..r.val,μ i (Y₂ w (projIcc 0 R hR s)))+∑ j,N₂ i j (realTimeClamp r.val) w := by
    filter_upwards [he₂] with w hw
    intro r i
    change Y₂ w r i-ξ₂ w i=0+_+_
    rw [hw]
    ring
  let q := fun t => ∫ w,‖prefixPath hR (Y₁ w-Y₂ w) t‖^2 ∂P
  let M := ∫ w,‖ξ₁ w-ξ₂ w‖^2 ∂P
  let D := (dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L
  have hD : 0≤D := by dsimp only [D];positivity
  have hq : Continuous q := prefix_square_moment_continuous P hR _ (hm₁.sub hm₂) (hi₁.sub hi₂)
  have hvpoint w : Y₁ w-Y₂ w-ContinuousMap.const (Icc (0:ℝ) R) (ξ₁ w-ξ₂ w)=V₁ w-V₂ w := by
    ext r i
    simp only [V₁,V₂,J₁,J₂,ContinuousMap.sub_apply,ContinuousMap.const_apply,Pi.sub_apply]
    ring
  have hstep t (ht : t∈Icc 0 R) : q t≤2*M+(2*D+1)*(∫ r in 0..t,q r) := by
    have hb := finite_picard_prefix_difference P hT F hF hle hnull W C hW hC hclock R hR hRT L hL
      μ σ hμ hσ hμLip hσLip (fun _ => 0) Y₁ Y₂ V₁ V₂ hm₁ hm₂ hi₁ hi₂ ha₁ ha₂ hv₁ hv₂ N₁ N₂ hn₁ hn₂ hI₁ hI₂ hvrep₁ hvrep₂ t ht
    have hs := initial_split_prefix_second_moment P R hR (fun w => Y₁ w-Y₂ w) (hm₁.sub hm₂) (hi₁.sub hi₂)
      (fun w => ξ₁ w-ξ₂ w) (hξm₁.sub hξm₂) (hξi₁.sub hξi₂) t
    simp_rw [hvpoint] at hs
    have hI : 0≤∫ r in 0..t,q r := intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => integral_nonneg (fun w => sq_nonneg _))
    change q t≤2*M+2*(∫ w,‖prefixPath hR (V₁ w-V₂ w) t‖^2 ∂P) at hs
    change (∫ w,‖prefixPath hR (V₁ w-V₂ w) t‖^2 ∂P)≤D*(∫ r in 0..t,q r) at hb
    nlinarith only [hb,hs,hI]
  have hg := Asakura.FullAudit.ch4_gronwall_written q (2*M) (2*D+1) R hR hq.continuousOn (by positivity) hstep R ⟨hR,le_rfl⟩
  simp only [q,prefix_path_endpoint] at hg
  convert hg using 1 <;> dsimp only [M,D] <;> ring

end Asakura.Chapter4.Vector
