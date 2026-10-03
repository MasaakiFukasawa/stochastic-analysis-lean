import Chapter9ActualForwardPDE
import Chapter9GaussianMixture

open Set MeasureTheory
open scoped ContDiff NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem spatial_directional_joint_continuous {d : ℕ}
    (F : ℝ × (Fin d → ℝ) → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (h : Fin d → ℝ) :
    ContinuousOn (fun z : ℝ × (Fin d → ℝ) => directional (fun y => F (z.1,y)) h z.2) (U ×ˢ univ) := by
  have hc := (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).clm_apply
    (continuousOn_const : ContinuousOn (fun _ : ℝ × (Fin d → ℝ) => ((0:ℝ),h)) (U ×ˢ univ))
  apply hc.congr
  intro z hz
  simpa only [iteratedFDeriv_one_apply] using (spatial_slice_first_jet F z.1 z.2 h (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz))).symm

theorem reverse_test_joint_continuous {d : ℕ}
    (F : ℝ × (Fin d → ℝ) → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (hp : ∀ z∈U ×ˢ univ,F z≠0)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContinuousOn (fun z : ℝ × (Fin d → ℝ) => reverseTest (fun y => F (z.1,y)) f z.2) (U ×ˢ univ) := by
  unfold reverseTest
  apply continuousOn_finsetSum
  intro i _
  have hc1 := ((directional_smooth f hf (Pi.single i 1)).continuous.comp (continuous_snd : Continuous (Prod.snd : ℝ × (Fin d → ℝ) → (Fin d → ℝ)))).continuousOn (s := U ×ˢ univ)
  have hc2 := ((directional_smooth _ (directional_smooth f hf (Pi.single i 1))
    (Pi.single i 1)).continuous.comp (continuous_snd : Continuous (Prod.snd : ℝ × (Fin d → ℝ) → (Fin d → ℝ)))).continuousOn (s := U ×ˢ univ)
  exact hc2.add (((show ContinuousOn (fun z : ℝ × (Fin d → ℝ) => z.2 i) (U ×ˢ univ) by fun_prop).add
    (continuousOn_const.mul ((spatial_directional_joint_continuous F U hU hF _).div hF.continuousOn hp))).mul hc1)

theorem reverse_test_zero_outside {d : ℕ} (p f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (hx : x∉tsupport f) : reverseTest p f x=0 := by
  have h1 (v : Fin d → ℝ) : directional f v x=0 := by
    unfold directional
    rw [fderiv_of_notMem_tsupport ℝ hx]
    rfl
  have h2 (v : Fin d → ℝ) : directional (directional f v) v x=0 := by
    have hn : x∉tsupport (directional f v) := fun hh => hx ((tsupport_fderiv_apply_subset ℝ v) hh)
    change (fderiv ℝ (directional f v) x) v=0
    rw [fderiv_of_notMem_tsupport ℝ hn]
    rfl
  unfold reverseTest
  simp only [h1,h2,mul_zero,add_zero,Finset.sum_const_zero]

/-- On every positive time strip the actual reverse generator applied to a
compact smooth test function is uniformly bounded, including outside its support. -/
theorem ou_reverse_generator_uniform_bound {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (ε T : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0≤C ∧ ∀ t∈Icc ε T,∀ y,
      ‖reverseTest (fun z => ∫ x,Real.exp (ouExponent x (t,z)) ∂μ) f y‖≤C := by
  let p := fun q => ∫ x,Real.exp (ouExponent x q) ∂μ
  have hsm : ContDiffOn ℝ ∞ p (Ioi 0 ×ˢ univ) := by
    exact (ou_gaussian_mixture_smooth μ).mono (fun z hz => hz.1)
  have hp (z : ℝ × (Fin d → ℝ)) (hz : z∈Ioi 0 ×ˢ univ) : p z≠0 := by
    have hv := ou_variance_positive z.1 hz.1
    exact (gaussian_mixture_positive μ (Real.exp (-z.1)) ⟨1-Real.exp (-2*z.1),hv.le⟩
      (by intro hz; exact hv.ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) hz)) z.2).2.ne'
  have hc := reverse_test_joint_continuous p (Ioi 0) isOpen_Ioi hsm hp f hf
  have hK : IsCompact (Icc ε T ×ˢ tsupport f) := isCompact_Icc.prod hfc.isCompact
  have hsub : Icc ε T ×ˢ tsupport f ⊆ Ioi 0 ×ˢ univ :=
    fun z hz => ⟨lt_of_lt_of_le hε hz.1.1,mem_univ _⟩
  obtain ⟨C,hC⟩ := hK.bddAbove_image (hc.norm.mono hsub)
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro t ht y
  by_cases hy : y∈tsupport f
  · exact (hC (mem_image_of_mem _ (show (t,y)∈Icc ε T ×ˢ tsupport f from ⟨ht,hy⟩))).trans (le_max_right _ _)
  · rw [reverse_test_zero_outside _ f y hy,norm_zero]
    exact le_max_left _ _
end Asakura.Chapter9
