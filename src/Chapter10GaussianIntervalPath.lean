import Chapter10GaussianContinuousPath

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology unitInterval
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A Gaussian continuous path on an arbitrary finite interval, including a
zero-length interval. -/
theorem gaussian_interval_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0≤T) (X : Ω → C(Icc (0:ℝ) T,E)) (hX : MemLp X 2 P)
    (hg : ∀ n (τ : Fin (n+1) → Icc (0:ℝ) T),HasGaussianLaw (fun w k => X w (τ k)) P) :
    HasGaussianLaw X P := by
  let a : C(unitInterval,Icc (0:ℝ) T) := ⟨fun u => ⟨T*u.val,
    mul_nonneg hT u.property.1,by nlinarith [u.property.2]⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk _⟩
  let b : C(Icc (0:ℝ) T,unitInterval) := ⟨fun s => projIcc 0 1 zero_le_one (s.val/T),
    continuous_projIcc.comp (continuous_subtype_val.div_const T)⟩
  have hab (s : Icc (0:ℝ) T) : a (b s)=s := by
    apply Subtype.ext
    change T*(projIcc 0 1 zero_le_one (s.val/T)).val=s.val
    by_cases hz : T=0
    · have hs : s.val=0 := le_antisymm (hz ▸ s.property.2) s.property.1
      simp [hz,hs]
    · have ht : 0<T := lt_of_le_of_ne hT (Ne.symm hz)
      have hq : s.val/T∈Icc (0:ℝ) 1 := ⟨div_nonneg s.property.1 hT,(div_le_one ht).mpr s.property.2⟩
      simp [projIcc,hq.1,hq.2,mul_div_cancel₀ _ hz,mul_comm T]
  let L : C(Icc (0:ℝ) T,E) →L[ℝ] C(unitInterval,E) := ContinuousMap.compCLM ℝ E a
  let Y := fun w => L (X w)
  have hY : MemLp Y 2 P := by
    apply hX.norm.of_le (L.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
    apply ae_of_all
    intro w
    simp only [norm_norm]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro u
    exact (X w).norm_coe_le_norm (a u)
  have hYg : HasGaussianLaw Y P := gaussian_continuous_path P Y hY (fun n => hg n (fun k => a (bernstein.z k)))
  have hh := hYg.map (show C(unitInterval,E) →L[ℝ] C(Icc (0:ℝ) T,E) from ContinuousMap.compCLM ℝ E b)
  apply hh.congr
  apply ae_of_all
  intro w
  ext s
  exact congrArg (X w) (hab s)

end Asakura.Chapter10
