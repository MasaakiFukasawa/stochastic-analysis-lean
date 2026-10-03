import Chapter4VectorFiniteLift
import Chapter4VectorPathRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable def realVectorPath {Ω : Type*} {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R : ℝ) (hRT : (R:EReal)<T) (w : Ω) : C(Icc (0:ℝ) R,Fin dim → ℝ) :=
  ⟨fun r => X (realTimeClamp r.val) w,continuous_iff_continuousAt.mpr (fun r =>
    (hc w _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hRT))).comp (f := fun s : Icc (0:ℝ) R => realTimeClamp s.val)
      (real_time_clamp_continuous.comp continuous_subtype_val).continuousAt)⟩

lemma real_vector_path_memLp_of_agreement
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (X : ClosedTime T → Ω → Fin dim → ℝ)
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (R d : ℝ) (hd : 0≤d) (hdR : d≤R) (hdT : (d:EReal)<T)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable[m] Y) (hi : MemLp Y 2 P)
    (he : ∀ᵐ w ∂P,∀ r,r∈Icc 0 d → X (realTimeClamp r) w=Y w (projIcc 0 R (hd.trans hdR) r)) :
    MemLp (realVectorPath X hc d hdT) 2 P := by
  have heq : realVectorPath X hc d hdT=ᵐ[P] fun w => restrictRealPath hdR (Y w) := by
    filter_upwards [he] with w hw
    apply ContinuousMap.ext
    intro r
    change X (realTimeClamp r.val) w=Y w ⟨r.val,r.property.1,r.property.2.trans hdR⟩
    simpa only [projIcc_of_mem (hd.trans hdR) ⟨r.property.1,r.property.2.trans hdR⟩] using hw r.val r.property
  exact (memLp_congr_ae heq).2 (restrict_real_path_memLp P hdR Y hm hi)

end Asakura.Chapter4.Vector
