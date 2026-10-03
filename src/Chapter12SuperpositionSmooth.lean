import Chapter12SuperpositionDerivative
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
universe u v
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem bounded_second_derivative_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (C : ℝ≥0)
    (hb : ∀ x,‖iteratedFDeriv ℝ 2 f x‖≤(C:ℝ)) :
    LipschitzWith C (fderiv ℝ f) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le (hdf.differentiable (by simp))
  intro x
  have he : ‖fderiv ℝ (fderiv ℝ f) x‖=‖iteratedFDeriv ℝ 2 f x‖ := by
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact_mod_cast he ▸ hb x

/-- Bounded derivatives give a smooth substitution map on the Banach
space of continuous paths. This supplies parameter regularity without
assuming smoothness of the ODE solution. -/
theorem continuousMap_superposition_smooth {K : Type v} {E F : Type u}
    [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ k : ℕ,1≤k → ∃ C : ℝ≥0,∀ x,‖iteratedFDeriv ℝ k f x‖≤(C:ℝ)) :
    ContDiff ℝ ∞ (continuousMapSuperposition (K:=K) f hf.continuous) := by
  have hall : ∀ n : ℕ,∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : E → F) (hf : ContDiff ℝ ∞ f),
      (∀ k : ℕ,1≤k → ∃ C : ℝ≥0,∀ x,‖iteratedFDeriv ℝ k f x‖≤(C:ℝ)) →
      ContDiff ℝ n (continuousMapSuperposition (K:=K) f hf.continuous) := by
    intro n
    induction n with
    | zero =>
      intro F _ _ _ f hf hb
      obtain ⟨C,hC⟩ := hb 2 (by omega)
      have hL := bounded_second_derivative_lipschitz f hf C hC
      change ContDiff ℝ 0 (continuousMapSuperposition (K:=K) f hf.continuous)
      apply contDiff_zero.mpr
      have hd : Differentiable ℝ (continuousMapSuperposition (K:=K) f hf.continuous) :=
        fun u => (superposition_hasFDerivAt f (fderiv ℝ f)
          (fun x => (hf.differentiable (by simp)).differentiableAt.hasFDerivAt) C hL u).differentiableAt
      exact hd.continuous
    | succ n ih =>
      intro F _ _ _ f hf hb
      obtain ⟨C,hC⟩ := hb 2 (by omega)
      have hL := bounded_second_derivative_lipschitz f hf C hC
      have hd := fun u : C(K,E) => superposition_hasFDerivAt f (fderiv ℝ f)
        (fun x => (hf.differentiable (by simp)).differentiableAt.hasFDerivAt) C hL u
      have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
      have hbd : ∀ k : ℕ,1≤k → ∃ C : ℝ≥0,∀ x,‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖≤(C:ℝ) := by
        intro k hk
        obtain ⟨L,hL⟩ := hb (k+1) (by omega)
        exact ⟨L,fun x => by rw [norm_iteratedFDeriv_fderiv];exact hL x⟩
      rw [show ((n+1:ℕ):ℕ∞ω)=(n:ℕ∞ω)+1 by simp,contDiff_succ_iff_fderiv]
      refine ⟨fun u => (hd u).differentiableAt,by simp,?_⟩
      have he : fderiv ℝ (continuousMapSuperposition (K:=K) f hf.continuous)=
          fun u => continuousMapApply (continuousMapSuperposition (fderiv ℝ f) hdf.continuous u) := by
        funext u
        exact (hd u).fderiv
      rw [he]
      exact (continuousMapApply (K:=K) (E:=E) (F:=F)).contDiff.comp (ih _ (fderiv ℝ f) hdf hbd)
  exact contDiff_infty.mpr (fun n => hall n F f hf hb)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.continuousMap_superposition_smooth
