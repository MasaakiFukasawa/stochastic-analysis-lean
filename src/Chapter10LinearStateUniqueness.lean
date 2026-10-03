import Chapter10StateVectorEquation
import Chapter10StateDriftRestriction
import Chapter10VectorNoisePath
import Chapter10LinearPathUniqueness

open MeasureTheory Set Filter
open scoped BigOperators NNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Any two actual solutions driven by the same Brownian system and initial
vector agree as continuous paths; the integral constructions need not coincide
pointwise on their exceptional sets. -/
theorem LinearStateWitness.unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (T : ℝ) (hT : 0≤T)
    (N M : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X Y : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hX : LinearStateWitness P B A G ξ T hT N X)
    (hY : LinearStateWitness P B A G ξ T hT M Y) : X=ᵐ[P] Y := by
  have hNM i j := ItoCovarianceFormula.unique P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W j) (N i j) (M i j) (fun z => G i j z.2) (B.martingale j)
    (hX.noise i j) (hY.noise i j) (hX.ito i j) (hY.ito i j)
  obtain ⟨Z,_,_,hZ⟩ := deterministic_vector_noise_path P B G hG N hX.noise hX.ito T hT
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  let A' := fun s => A (projIcc 0 T hT s).val
  have hAc : Continuous A' := hA.comp (continuous_subtype_val.comp continuous_projIcc)
  have hAK s : ‖A' s‖≤K := (hC _ (projIcc 0 T hT s).property).trans (le_max_left C 0)
  have he s (hs : s∈Icc (0:ℝ) T) : A' s=A s := by
    simp only [A']
    congr 1
    simp [projIcc,hs.1,hs.2]
  have hX' := hX.congr_drift P B A A' G ξ T hT N X he
  have hY' := hY.congr_drift P B A A' G ξ T hT M Y he
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hNM i j))] with w hw
  apply linear_forced_paths_unique A' hAc K hAK T hT (ξ w,Z w) _ _
  · intro t
    rw [hX'.vector_real_equation P B A' hAc G ξ T hT N X w t]
    congr 1
    ext i
    exact (hZ w t i).symm
  · intro t
    rw [hY'.vector_real_equation P B A' hAc G ξ T hT M Y w t]
    congr 1
    ext i
    rw [hZ w t i]
    apply Finset.sum_congr rfl
    intro j _
    exact (hw i j _ (half_real_time_finite t.val)).symm

end Asakura.Chapter10
