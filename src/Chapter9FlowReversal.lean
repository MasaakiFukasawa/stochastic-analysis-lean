import Chapter9TimeDependentFlowC1

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Reversing a solution of the actual integral equation gives the integral
equation with reversed, negated velocity. -/
theorem integral_path_time_reversal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (b : ℝ → E → E)
    (hb : Continuous b.uncurry) (X : ℝ → E) (hcX : Continuous X)
    (x : E) (T : ℝ) (hT : 0≤T)
    (hX : ∀ s∈Icc 0 T,X s=x+∫ r in 0..s,b r (X r)) :
    ∀ s∈Icc 0 T,X (T-s)=X T+∫ r in 0..s,-b (T-r) (X (T-r)) := by
  have hc : Continuous (fun r => b r (X r)) := hb.comp (continuous_id.prodMk hcX)
  intro s hs
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_comp_sub_left (fun r => b r (X r)) T,sub_zero,
    hX (T-s) ⟨sub_nonneg.mpr hs.2,by linarith [hs.1]⟩,hX T ⟨hT,le_rfl⟩]
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (T-s)) (hc.intervalIntegrable (T-s) T)
  rw [←he]
  abel

 theorem integral_path_unique {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (b : ℝ → E → E)
    (hb : Continuous b.uncurry) (K : ℝ≥0) (hK : ∀ t,LipschitzWith K (b t))
    (X Y : ℝ → E) (hcX : Continuous X) (hcY : Continuous Y) (x : E)
    (T : ℝ) (hT : 0≤T)
    (hX : ∀ s∈Icc 0 T,X s=x+∫ r in 0..s,b r (X r))
    (hY : ∀ s∈Icc 0 T,Y s=x+∫ r in 0..s,b r (Y r)) :
    ∀ s∈Icc 0 T,X s=Y s := by
  have h := time_dependent_initial_stability b K hb hK X Y (fun _ => 0) hcX hcY x x T hT
    (fun s hs => by simpa only [add_zero] using hX s hs)
    (fun s hs => by simpa only [add_zero] using hY s hs)
  intro s hs
  have hh := h s hs
  simp only [sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

/-- Forward and backward solution families are genuine inverse maps. -/
theorem integral_flow_inverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (b : ℝ → E → E)
    (hb : Continuous b.uncurry) (K : ℝ≥0) (hK : ∀ t,LipschitzWith K (b t))
    (X Y : E → ℝ → E) (hcX : ∀ x,Continuous (X x)) (hcY : ∀ x,Continuous (Y x))
    (T : ℝ) (hT : 0≤T)
    (hX : ∀ x s,s∈Icc 0 T → X x s=x+∫ r in 0..s,b r (X x r))
    (hY : ∀ y s,s∈Icc 0 T → Y y s=y+∫ r in 0..s,-b (T-r) (Y y r)) :
    (∀ x,Y (X x T) T=x) ∧ (∀ y,X (Y y T) T=y) := by
  let c := fun r y => -b (T-r) y
  have hc : Continuous c.uncurry := (hb.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg
  have hKc r : LipschitzWith K (c r) := (hK (T-r)).neg
  constructor
  · intro x
    have hr := integral_path_time_reversal b hb (X x) (hcX x) x T hT (hX x)
    have he := integral_path_unique c hc K hKc (fun s => X x (T-s)) (Y (X x T))
      ((hcX x).comp (continuous_const.sub continuous_id)) (hcY _) (X x T) T hT hr (hY _)
    have hh := he T ⟨hT,le_rfl⟩
    have h0 := hX x 0 ⟨le_rfl,hT⟩
    simpa only [sub_self,intervalIntegral.integral_same,add_zero] using hh.symm.trans (by simpa using h0)
  · intro y
    have hr := integral_path_time_reversal c hc (Y y) (hcY y) y T hT (hY y)
    have hr' : ∀ s∈Icc 0 T,Y y (T-s)=Y y T+∫ r in 0..s,b r (Y y (T-r)) := by
      simpa only [c,sub_sub_cancel,neg_neg] using hr
    have he := integral_path_unique b hb K hK (fun s => Y y (T-s)) (X (Y y T))
      ((hcY y).comp (continuous_const.sub continuous_id)) (hcX _) (Y y T) T hT hr' (hX _)
    have hh := he T ⟨hT,le_rfl⟩
    have h0 := hY y 0 ⟨le_rfl,hT⟩
    simpa only [sub_self,intervalIntegral.integral_same,add_zero] using hh.symm.trans (by simpa using h0)
end Asakura.Chapter9
