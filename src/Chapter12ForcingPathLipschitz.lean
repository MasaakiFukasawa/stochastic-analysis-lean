import Chapter10ForcedPathStability
import Chapter12ContinuousPathPrimitive

open MeasureTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem forcing_path_lipschitz {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b)
    (T : ℝ) (hT : 0≤T)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hS : ∀q t,S q t=q t+∫s in 0..t.val,b (S q (projIcc 0 T hT s))) :
    LipschitzWith ⟨Real.exp (((K:ℝ)+1)*T),(Real.exp_pos _).le⟩ S := by
  apply LipschitzWith.of_dist_le_mul
  change ∀ q r,dist (S q) (S r) ≤ Real.exp (((K:ℝ)+1)*T)*dist q r
  intro q r
  rw [dist_eq_norm,dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  let p := projIcc 0 T hT
  have hp : Continuous p := continuous_projIcc
  have hq : ∀s,s∈Icc 0 T → (S q) (p s)=0+(∫u in 0..s,b (S q (p u)))+q (p s) := by
    intro s hs
    have he : (p s).val=s := congrArg Subtype.val (projIcc_of_mem hT hs)
    have hh := hS q (p s)
    rw [he] at hh
    simpa only [zero_add,add_comm] using hh
  have hr : ∀s,s∈Icc 0 T → (S r) (p s)=0+(∫u in 0..s,b (S r (p u)))+r (p s) := by
    intro s hs
    have he : (p s).val=s := congrArg Subtype.val (projIcc_of_mem hT hs)
    have hh := hS r (p s)
    rw [he] at hh
    simpa only [zero_add,add_comm] using hh
  have hh := Asakura.Chapter10.time_dependent_forced_path_stability (fun _ x => b x) K
    (hb.continuous.comp continuous_snd) (fun _ => hb)
    (fun s => S q (p s)) (fun s => S r (p s)) (fun s => q (p s)) (fun s => r (p s))
    ((S q).continuous.comp hp) ((S r).continuous.comp hp) 0 0 T ‖q-r‖ hT (norm_nonneg _)
    (fun s _ => (q-r).norm_coe_le_norm (p s)) hq hr t.val t.property
  have ht : p t.val=t := projIcc_of_mem hT t.property
  simpa only [ht,sub_self,norm_zero,zero_add,ContinuousMap.sub_apply,NNReal.coe_mk] using hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.forcing_path_lipschitz
