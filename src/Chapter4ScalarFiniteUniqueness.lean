import Chapter4FinitePicardDifference
import Chapter4VolterraPathLimit
import Chapter4PathEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Scalar pathwise uniqueness on a finite horizon: the SDE's own two Ito
integrals yield the Gronwall inequality, and zero L² path norm yields one
common exceptional set for all times. -/
theorem scalar_sde_finite_unique_L2
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
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) R,ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (ha₁ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₁ w r))
    (ha₂ : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => Y₂ w r))
    (N₁ N₂ : ClosedTime T → Ω → ℝ)
    (hn₁ : LocalMProcessWitness P F N₁) (hn₂ : LocalMProcessWitness P F N₂)
    (hI₁ : ItoCovarianceFormula P F W
      (fun z => σ (Y₁ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N₁)
    (hI₂ : ItoCovarianceFormula P F W
      (fun z => σ (Y₂ z.1 (finitePrefixTime (T := T) R hR (realTimeClamp z.2)))) N₂)
    (he₁ : ∀ᵐ w ∂P,∀ r,Y₁ w r=ξ w+(∫ s in 0..r.val,μ (Y₁ w (projIcc 0 R hR s)))+N₁ (realTimeClamp r.val) w)
    (he₂ : ∀ᵐ w ∂P,∀ r,Y₂ w r=ξ w+(∫ s in 0..r.val,μ (Y₂ w (projIcc 0 R hR s)))+N₂ (realTimeClamp r.val) w)
    : Y₁=ᵐ[P] Y₂ := by
  letI : MeasurableSpace Ω := m
  let u := fun t => ∫ w,‖prefixPath hR (Y₁ w-Y₂ w) t‖^2 ∂P
  let c := (2*R+8)*L
  have hc : 0≤c := by dsimp [c]; positivity
  have hu : Continuous u := prefix_square_moment_continuous P hR _ (hm₁.sub hm₂) (hi₁.sub hi₂)
  have hstep t (ht : t∈Icc 0 R) : u t≤c*∫ r in 0..t,u r :=
    finite_picard_prefix_difference P hT F hF hle hnull W C hW hC hCm hCc hclock R hR hRT
      L hL μ σ hμ hσ hLip ξ Y₁ Y₂ Y₁ Y₂ hm₁ hm₂ hi₁ hi₂ ha₁ ha₂ hm₁ hm₂
      N₁ N₂ hn₁ hn₂ hI₁ hI₂ he₁ he₂ t ht
  have hb := ch4_gronwall_global u hu 0 (c+1) R (by linarith) hR (by
    intro t ht
    have hpos : 0≤∫ r in 0..t,u r := intervalIntegral.integral_nonneg_of_forall ht.1
      (fun r => integral_nonneg (fun w => sq_nonneg _))
    have h := hstep t ht
    linarith only [h,hpos])
  have hz := hb R ⟨hR,le_rfl⟩
  simp only [u,prefix_path_endpoint,zero_mul] at hz
  have he : (∫ w,‖Y₁ w-Y₂ w‖^2 ∂P)=0 := le_antisymm hz (integral_nonneg (fun w => sq_nonneg _))
  exact paths_equal_of_zero_second_moment P Y₁ Y₂ (hi₁.sub hi₂) he

end Asakura.Chapter4
