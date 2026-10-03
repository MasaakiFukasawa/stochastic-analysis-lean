import FullAuditHeatKernel
import Chapter5DerivativeGluing

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 4000000

noncomputable def heatTaylorNegative (h : ℕ → ℝ → ℝ) (j k : ℕ) (p : ℝ × ℝ) : ℝ :=
  match j with
  | 0 => h k p.2+p.1/2*h (k+2) p.2+p.1^2/8*h (k+4) p.2+p.1^3/48*h (k+6) p.2
  | 1 => h (k+2) p.2/2+p.1/4*h (k+4) p.2+p.1^2/16*h (k+6) p.2
  | 2 => h (k+4) p.2/4+p.1/8*h (k+6) p.2
  | _ => h (k+6) p.2/8

noncomputable def heatTaylorJet (h : ℕ → ℝ → ℝ) (j k : ℕ) (p : ℝ × ℝ) : ℝ :=
  if 0≤p.1 then (1/2:ℝ)^j*heatAverage (h (2*j+k)) p.2 p.1 else heatTaylorNegative h j k p

lemma heatTaylorNegative_zero (h : ℕ → ℝ → ℝ) (j k : ℕ) (hj : j≤3) (x : ℝ) :
    heatTaylorNegative h j k (0,x)=(1/2:ℝ)^j*h (2*j+k) x := by
  interval_cases j <;> simp [heatTaylorNegative,Nat.add_comm] <;> ring

lemma heatTaylorNegative_continuous (h : ℕ → ℝ → ℝ) (hc : ∀ k,Continuous (h k)) (j k : ℕ) :
    Continuous (heatTaylorNegative h j k) := by
  change Continuous (fun p : ℝ × ℝ => heatTaylorNegative h j k p)
  cases j with
  | zero => dsimp only [heatTaylorNegative]; fun_prop
  | succ j => cases j with
    | zero => dsimp only [heatTaylorNegative]; fun_prop
    | succ j => cases j with
      | zero => dsimp only [heatTaylorNegative]; fun_prop
      | succ j => dsimp only [heatTaylorNegative]; fun_prop

/-- Joint continuity across time zero is derived from the exact matching
Taylor coefficients, before any derivative at zero is used. -/
theorem heatTaylorJet_continuous (h : ℕ → ℝ → ℝ) (hc : ∀ k,Continuous (h k))
    (B : ℕ → ℝ) (hb : ∀ k x,‖h k x‖≤B k) (j k : ℕ) (hj : j≤3) :
    Continuous (heatTaylorJet h j k) := by
  apply Continuous.if_le
    (continuous_const.mul ((heatAverage_continuous (hc _) (B _) (hb _)).comp
      (continuous_snd.prodMk continuous_fst)))
    (heatTaylorNegative_continuous h hc j k) continuous_const continuous_fst
  rintro ⟨t,x⟩ hp
  change 0=t at hp
  subst t
  simpa only [Function.comp_apply,Pi.mul_apply,heatAverage_zero] using (heatTaylorNegative_zero h j k hj x).symm

end Asakura.Chapter5
