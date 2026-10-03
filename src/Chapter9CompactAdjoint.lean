import Chapter9ReverseGenerator
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp

open MeasureTheory Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def directional {d : ℕ} (f : (Fin d → ℝ) → ℝ) (v : Fin d → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => fderiv ℝ f x v

theorem directional_smooth {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) : ContDiff ℝ ∞ (directional f v) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem compact_directional_ibp {d : ℕ} (f g : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfc : HasCompactSupport f)
    (v : Fin d → ℝ) :
    (∫ x,f x*directional g v x)= -(∫ x,directional f v x*g x) := by
  have hdf := directional_smooth f hf v
  have hdg := directional_smooth g hg v
  have hdfc : HasCompactSupport (directional f v) := hfc.fderiv_apply ℝ v
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hdfc.mul_right
  · exact (hf.continuous.mul hdg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  · intro x _; exact hf.differentiable (by simp) x
  · intro x _; exact hg.differentiable (by simp) x

theorem compact_second_directional_ibp {d : ℕ} (f g : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfc : HasCompactSupport f)
    (v : Fin d → ℝ) :
    (∫ x,f x*directional (directional g v) v x)=
      ∫ x,directional (directional f v) v x*g x := by
  rw [compact_directional_ibp f (directional g v) hf (directional_smooth g hg v) hfc v,
    compact_directional_ibp (directional f v) g (directional_smooth f hf v) hg (hfc.fderiv_apply ℝ v) v,
    neg_neg]

/-- The adjoint identity used in the reverse-generator calculation follows
from two genuine integrations by parts. Compact support removes all
boundary terms; no decay of the other smooth factor is assumed. -/
theorem ou_adjoint_compact {d : ℕ} (q k : (Fin d → ℝ) → ℝ)
    (hq : ContDiff ℝ ∞ q) (hk : ContDiff ℝ ∞ k) (hqc : HasCompactSupport q) :
    (∫ x,q x*(Finset.sum Finset.univ (fun i : Fin d => directional (directional k (Pi.single i 1)) (Pi.single i 1) x-
      x i*directional k (Pi.single i 1) x)))=
    ∫ x,(Finset.sum Finset.univ (fun i : Fin d => directional (directional q (Pi.single i 1)) (Pi.single i 1) x+
      directional (fun y : Fin d → ℝ => y i*q y) (Pi.single i 1) x))*k x := by
  let e : Fin d → (Fin d → ℝ) := fun i => Pi.single i 1
  have hqi i : ContDiff ℝ ∞ (fun x : Fin d → ℝ => x i*q x) := by fun_prop
  have hqic i : HasCompactSupport (fun x : Fin d → ℝ => x i*q x) := hqc.mul_left
  have hi1 i : Integrable (fun x => q x*directional (directional k (e i)) (e i) x) :=
    (hq.continuous.mul (directional_smooth _ (directional_smooth k hk _) _).continuous).integrable_of_hasCompactSupport hqc.mul_right
  have hi2 i : Integrable (fun x => q x*(x i*directional k (e i) x)) :=
    (hq.continuous.mul ((show Continuous (fun x : Fin d → ℝ => x i) by fun_prop).mul
      (directional_smooth k hk _).continuous)).integrable_of_hasCompactSupport hqc.mul_right
  have hj1 i : Integrable (fun x => directional (directional q (e i)) (e i) x*k x) :=
    ((directional_smooth _ (directional_smooth q hq _) _).continuous.mul hk.continuous).integrable_of_hasCompactSupport
      ((hqc.fderiv_apply ℝ (e i)).fderiv_apply ℝ (e i)).mul_right
  have hj2 i : Integrable (fun x => directional (fun y => y i*q y) (e i) x*k x) :=
    ((directional_smooth _ (hqi i) _).continuous.mul hk.continuous).integrable_of_hasCompactSupport
      ((hqic i).fderiv_apply ℝ (e i)).mul_right
  simp_rw [Finset.mul_sum,Finset.sum_mul,mul_sub,add_mul]
  have hleft := integral_finsetSum Finset.univ (fun i _ => (hi1 i).sub (hi2 i))
  have hright := integral_finsetSum Finset.univ (fun i _ => (hj1 i).add (hj2 i))
  dsimp only [Pi.sub_apply,Pi.add_apply,e] at hleft hright
  rw [hleft,hright]
  apply sum_congr rfl
  intro i _
  rw [integral_sub (hi1 i) (hi2 i),integral_add (hj1 i) (hj2 i),
    compact_second_directional_ibp q k hq hk hqc (e i)]
  have he := compact_directional_ibp (fun x : Fin d → ℝ => x i*q x) k (hqi i) hk (hqic i) (e i)
  have hm : (fun x : Fin d → ℝ => q x*(x i*directional k (e i) x))=
      (fun x => (x i*q x)*directional k (e i) x) := by funext x; ring
  rw [hm,he,sub_neg_eq_add]
end Asakura.Chapter9
