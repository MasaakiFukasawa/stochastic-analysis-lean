import Chapter8AdditivePathMap

open Set MeasureTheory
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Stability of any continuous-path realization of the additive SDE
solution map, derived from its integral equation. -/
theorem additive_solution_path_stability {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b) (T : ℝ) (hT : 0≤T)
    (S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hS : ∀ p t,S p t=p.1+(∫ s in 0..t.val,b (S p (projIcc 0 T hT s)))+p.2 t)
    (x : E) (u v : C(Icc (0:ℝ) T,E)) :
    ‖S (x,u)-S (x,v)‖≤Real.exp (((K:ℝ)+1)*T)*‖u-v‖ := by
  let X := fun t => S (x,u) (projIcc 0 T hT t)
  let Y := fun t => S (x,v) (projIcc 0 T hT t)
  have hp (t : ℝ) (ht : t∈Icc 0 T) : (projIcc 0 T hT t).val=t := by
    simp [projIcc,ht.1,ht.2]
  have hx : ∀ t,t∈Icc 0 T → X t=x+(∫ s in 0..t,b (X s))+u (projIcc 0 T hT t) := by
    intro t ht
    dsimp only [X]
    rw [hS,hp t ht]
  have hy : ∀ t,t∈Icc 0 T → Y t=x+(∫ s in 0..t,b (Y s))+v (projIcc 0 T hT t) := by
    intro t ht
    dsimp only [Y]
    rw [hS,hp t ht]
  have he := Asakura.Chapter8.forced_path_stability b K hb X Y
    (fun s => u (projIcc 0 T hT s)) (fun s => v (projIcc 0 T hT s))
    ((S (x,u)).continuous.comp continuous_projIcc)
    ((S (x,v)).continuous.comp continuous_projIcc)
    x x T ‖u-v‖ hT (norm_nonneg _)
    (fun s _ => (u-v).norm_coe_le_norm _) hx hy
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hh := he t.val t.property
  have heq : projIcc 0 T hT t.val=t := Subtype.ext (hp t.val t.property)
  simpa only [X,Y,heq,sub_self,norm_zero,zero_add,ContinuousMap.sub_apply] using hh

end Asakura.Chapter12
