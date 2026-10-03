import Chapter11ExponentialDensityDecomposition
import Chapter3IncreasingAdaptedVariation
import Chapter13HJMPrimitive

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter11
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness of the semimartingale decomposition removes the entire drift. -/
theorem local_semimartingale_drift_constant {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (X A M:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A M)
    (hL:LocalMProcessWitness P F (fun t w => X t w-X ⊥ w)) :
    ∀ᵐw∂P,∀t,t<⊤ → A t w=A ⊥ w := by
  have hXm:Measurable[F ⊥] (X ⊥) := by
    have he:X ⊥=(fun w => A ⊥ w+M ⊥ w) := funext (hX.decomposition ⊥ hT)
    rw [he]
    exact (hX.variation.adapted ⊥ hT).add (hX.martingale.adapted P F ⊥ hT)
  have hAv:=continuous_increasing_adapted_variation hT F hF (fun _ w => X ⊥ w)
    (fun _ _ => hXm.mono (hF bot_le) le_rfl) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ _ _ => continuousAt_const)
  have hother:SemimartingaleDecomposition P F X (fun _ w => X ⊥ w) (fun t w => X t w-X ⊥ w) :=
    ⟨hAv,hL,hX.continuous,fun t ht w => by ring⟩
  filter_upwards [hX.unique P F hF hle hother] with w hw
  intro t ht
  exact (hw t ht).1.trans (hw ⊥ hT).1.symm

/-- A vanishing primitive has zero density, on the positive time axis. -/
theorem zero_primitive_density (b:ℝ → ℝ) (hb:LocallyIntegrable b volume)
    (he:∀r,0≤r → ∫s in 0..r,b s=0) :
    ∀ᵐr∂volume,0<r → b r=0 := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hb] with r hr
  intro hr0
  have hevent:(fun x => ∫s in 0..x,b s)=ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hr0] with x hx
    exact he x hx.le
  have hd:HasDerivAt (fun _ :ℝ => (0:ℝ)) (b r) r := (hr 0).congr_of_eventuallyEq hevent.symm
  exact hd.unique (hasDerivAt_const r 0)


theorem zero_primitive_density_on (b:ℝ → ℝ) (R:ℝ) (hR:0≤R)
    (hb:IntervalIntegrable b volume 0 R)
    (he:∀r∈Icc 0 R,∫s in 0..r,b s=0) :
    ∀ᵐr∂volume,r∈Ioo 0 R → b r=0 := by
  filter_upwards [_root_.IntervalIntegrable.ae_hasDerivAt_integral hb] with r hr
  intro hr0
  have hrd:=hr (by simpa only [uIcc_of_le hR] using Ioo_subset_Icc_self hr0) 0 (by simp [uIcc_of_le hR,hR])
  have hevent:(fun x => ∫s in 0..x,b s)=ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
    filter_upwards [Ioo_mem_nhds hr0.1 hr0.2] with x hx
    exact he x (Ioo_subset_Icc_self hx)
  have hd:HasDerivAt (fun _ :ℝ => (0:ℝ)) (b r) r := hrd.congr_of_eventuallyEq hevent.symm
  exact hd.unique (hasDerivAt_const r 0)

end Asakura.Chapter13
#print axioms Asakura.Chapter13.local_semimartingale_drift_constant
#print axioms Asakura.Chapter13.zero_primitive_density

#print axioms Asakura.Chapter13.zero_primitive_density_on
