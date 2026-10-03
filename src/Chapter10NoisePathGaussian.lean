import Chapter10JointPathGaussian
import Chapter10InitialNoiseFiniteLaw
import Chapter10VectorNoisePath

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The actual vector noise path is jointly Gaussian with the initial vector. -/
theorem initial_noise_path_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n k : ℕ} (B : BrownianSystem P n)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (ξ : Ω → Fin k → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξg : HasGaussianLaw ξ P)
    (T : ℝ) (hT : 0≤T) :
    ∃ Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ),Measurable Z ∧ MemLp Z 2 P ∧
      (∀ w t i,Z w t i=∑ j,N i j (realTimeClamp t.val) w) ∧
      HasGaussianLaw (fun w => (ξ w,Z w)) P := by
  obtain ⟨Z,hm,hZ,he⟩ := deterministic_vector_noise_path P B G hG N hN hNI T hT
  refine ⟨Z,hm,hZ,he,?_⟩
  apply initial_path_joint_gaussian P T hT ξ hξg.memLp_two Z hZ
  intro p τ
  have hg := initial_noise_finite_law P B G hG N hN hNI ξ hξ hξg T hT (p+1) τ
  have heq : (fun w a => (ξ w,Z w (τ a))) =
      (fun w a => (ξ w,fun i => ∑ j,N i j (realTimeClamp (τ a).val) w)) := by
    funext w a
    congr 1
    funext i
    exact he w (τ a) i
  rw [heq]
  exact hg

end Asakura.Chapter10
