import Chapter12GaussianJetIntegration
import Chapter12DivergencePowerIBP

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def gaussianArrayNorm {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) (x : Fin n → ℝ) : ℝ := Real.sqrt (∑ i,(f i).f x^2)

theorem gaussianArrayNorm_nonneg {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) (x : Fin n → ℝ) : 0≤gaussianArrayNorm f x := Real.sqrt_nonneg _

theorem gaussianArrayNorm_continuous {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) : Continuous (gaussianArrayNorm f) := by
  exact (continuous_finset_sum _ (fun i _ => (f i).smooth.continuous.pow 2)).sqrt

theorem gaussianArrayNorm_growth {n : ℕ} {I : Type*} [Fintype I]
    (f : I → GaussianJet n) : PolyGrowth (gaussianArrayNorm f) := by
  classical
  have hg : PolyGrowth (fun x => 1+∑ i,(f i).f x^2) :=
    (PolyGrowth.const 1).add (PolyGrowth.finset_sum _ _
      (fun i _ => polynomial_growth_pow (f i).polynomial_growth 2))
  obtain ⟨C,hC,a,ha⟩ := hg
  refine ⟨C,hC,a,fun x => ?_⟩
  have hsum : 0≤∑ i,(f i).f x^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hsum
  have hn := Real.sqrt_nonneg (∑ i,(f i).f x^2)
  have hh : Real.sqrt (∑ i,(f i).f x^2)≤1+∑ i,(f i).f x^2 := by nlinarith [sq_nonneg (Real.sqrt (∑ i,(f i).f x^2)-1)]
  rw [abs_of_nonneg (gaussianArrayNorm_nonneg f x)]
  exact hh.trans ((le_abs_self _).trans (ha x))

noncomputable def gaussianDerivativeArray {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (k : ℕ)
    (b : Fin (k+1) → Fin (n+1)) : GaussianJet (n+1) :=
  (u (b 0)).iteratedPartial (List.ofFn (fun j : Fin k => b j.succ))

noncomputable def gaussianDerivativeNorm {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (k : ℕ) : (Fin (n+1) → ℝ) → ℝ :=
  gaussianArrayNorm (gaussianDerivativeArray u k)

noncomputable def gaussianSobolevSum {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (m : ℕ) (x : Fin (n+1) → ℝ) : ℝ :=
  ∑ k : Fin (m+1),gaussianDerivativeNorm u k x

theorem gaussianSobolevSum_nonneg {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (m : ℕ) (x : Fin (n+1) → ℝ) :
    0≤gaussianSobolevSum u m x := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem gaussianSobolevSum_power_integrable {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (m q : ℕ) :
    Integrable (fun x => gaussianSobolevSum u m x^q) (Measure.pi fun _ => gaussianReal 0 1) := by
  have hc : Continuous (gaussianSobolevSum u m) :=
    continuous_finset_sum _ (fun k _ => gaussianArrayNorm_continuous _)
  have hg : PolyGrowth (gaussianSobolevSum u m) :=
    PolyGrowth.finset_sum _ _ (fun k _ => gaussianArrayNorm_growth _)
  exact memLp_one_iff_integrable.mp (polynomial_growth_gaussian_memLp
    (hc.pow q).measurable (polynomial_growth_pow hg q) 1 (by simp))

end Asakura.Chapter12
