import Chapter8BrownianForcingPath
import Chapter8AdditiveUniqueness

open MeasureTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The canonical continuous-forcing solution is the actual SDE solution,
simultaneously at all times on a finite interval, for each initial point. -/
theorem sde_canonical_identification {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n) (b : (Fin d → ℝ) → (Fin d → ℝ))
    (σ : Fin d → Fin n → ℝ) (L : ℝ≥0) (hb : LipschitzWith L b)
    (T : ℝ) (hT : 0≤T) (V : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hV : ∀ w t i,V w t i=∑ j,σ i j*B.W j (realTimeClamp t.val) w)
    (S : (Fin d → ℝ) × C(Icc (0:ℝ) T,Fin d → ℝ) → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hS : ∀ p t,S p t=p.1+(∫ s in 0..t.val,b (S p (projIcc 0 T hT s)))+p.2 t)
    (x : Fin d → ℝ) (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) X) :
    ∀ᵐ w ∂P,∀ t : Icc (0:ℝ) T, X (realTimeClamp t.val) w=S (x,V w) t := by
  have hXc w : Continuous (fun r => X (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  filter_upwards [sde_additive_equation P B (fun i y => b y i) σ x X hX] with w hw
  let Y := fun r => S (x,V w) (projIcc 0 T hT r)
  let W := fun r => V w (projIcc 0 T hT r)
  have hx r (hr : r∈Icc 0 T) : X (realTimeClamp r) w=x+(∫ s in 0..r,b (X (realTimeClamp s) w))+W r := by
    ext i
    have hp := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
      ((hb.continuous.comp (hXc w)).intervalIntegrable 0 r (μ := volume))
    have hv : W r i=∑ j,σ i j*B.W j (realTimeClamp r) w := by
      dsimp only [W]
      rw [hV]
      simp only [projIcc_of_mem hT hr]
    change X (realTimeClamp r) w i=x i+(∫ s in 0..r,b (X (realTimeClamp s) w)) i+W r i
    change (∫ s in 0..r,b (X (realTimeClamp s) w) i)=(∫ s in 0..r,b (X (realTimeClamp s) w)) i at hp
    rw [← hp,hv]
    exact hw r hr.1 i
  have hy r (hr : r∈Icc 0 T) : Y r=x+(∫ s in 0..r,b (Y s))+W r := by
    have hp : projIcc 0 T hT r=⟨r,hr⟩ := projIcc_of_mem hT hr
    change S (x,V w) (projIcc 0 T hT r)=_
    rw [hp,hS]
    simp only [Y,W,hp]
  intro t
  have he := additive_path_unique b L hb (fun r => X (realTimeClamp r) w) Y W
    (hXc w) ((S (x,V w)).continuous.comp continuous_projIcc) x T hT hx hy t.val t.property
  simpa only [Y,projIcc_of_mem hT t.property] using he

end Asakura.Chapter8
