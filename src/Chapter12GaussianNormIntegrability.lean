import Chapter12GaussianJetLinearProjection
import Chapter12GaussianArrayNorm

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem gaussian_array_norm_power_integrable {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) (q : ℕ) :
    Integrable (fun x => gaussianArrayNorm f x^q) (Measure.pi (fun _ => gaussianReal 0 1)) :=
  memLp_one_iff_integrable.mp (polynomial_growth_gaussian_memLp
    ((gaussianArrayNorm_continuous f).pow q).measurable
    (polynomial_growth_pow (gaussianArrayNorm_growth f) q) 1 (by simp))

noncomputable def gaussianLinearFormJet {n : ℕ} (a : Fin n → ℝ) : GaussianJet n :=
  GaussianJet.finsetSum Finset.univ (fun i => (GaussianJet.coordinate i).smul (a i))

theorem gaussianLinearFormJet_apply {n : ℕ} (a x : Fin n → ℝ) :
    (gaussianLinearFormJet a).f x=∑ i,a i*x i := rfl

theorem gaussian_matrix_norm_power_integrable {n : ℕ} {I : Type*} [Fintype I]
    (a : I → Fin n → ℝ) (q : ℕ) :
    Integrable (fun z : Fin n → ℝ => (Real.sqrt (∑ i,(∑ j,a i j*z j)^2))^q)
      (Measure.pi (fun _ => gaussianReal 0 1)) :=
  gaussian_array_norm_power_integrable (fun i => gaussianLinearFormJet (a i)) q

theorem gaussian_sum_array_norm_power_integrable {n : ℕ} {I : Type*} [Fintype I]
    {J : I → Type*} [∀ i,Fintype (J i)] (f : ∀ i,J i → GaussianJet n) (q : ℕ) :
    Integrable (fun x => (∑ i,gaussianArrayNorm (f i) x)^q)
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
  have hc : Continuous (fun x => ∑ i,gaussianArrayNorm (f i) x) :=
    continuous_finset_sum _ (fun i _ => gaussianArrayNorm_continuous (f i))
  have hg : PolyGrowth (fun x => ∑ i,gaussianArrayNorm (f i) x) :=
    PolyGrowth.finset_sum _ _ (fun i _ => gaussianArrayNorm_growth (f i))
  exact memLp_one_iff_integrable.mp (polynomial_growth_gaussian_memLp
    (hc.pow q).measurable (polynomial_growth_pow hg q) 1 (by simp))

end Asakura.Chapter12
