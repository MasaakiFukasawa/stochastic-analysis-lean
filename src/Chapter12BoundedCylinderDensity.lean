import Chapter12ConditionalLp
import Chapter12FiniteVectorLp

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The bounded-variable part of the manuscript's Lp density argument. -/
theorem bounded_cylinder_Lp_density {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)]
    [∀ n, BorelSpace (E n)]
    (X : (n : ℕ) → Ω → E n) (hX : ∀ n, Measurable (X n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (X n) inferInstance))
    (U : Lp ℝ 2 P)
    (hU : AEStronglyMeasurable[⨆ n, MeasurableSpace.comap (X n) inferInstance] U P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ w ∂P, |U w| ≤ C)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (g : E n → ℝ), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (fun w => U w-g (X n w)) p P < ENNReal.ofReal ε := by
  let G := fun n => MeasurableSpace.comap (X n) inferInstance
  have hle : ∀ n, G n ≤ m := fun n => (hX n).comap_le
  have ht := conditional_upward_bounded_Lp P G hmono hle U hU C hC hb p hp hpt
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hε)))).exists
  let V : Lp ℝ 2 P := condExpL2 ℝ ℝ (hle n) U
  have hVm : AEStronglyMeasurable[G n] V P := aestronglyMeasurable_condExpL2 (hle n) U
  obtain ⟨f,hf,he⟩ := hVm.stronglyMeasurable_mk.measurable.exists_eq_measurable_comp
  have hVf : (V : Ω → ℝ) =ᵐ[P] f ∘ X n := by
    simpa only [he] using hVm.ae_eq_mk
  have hVi : MemLp (V : Ω → ℝ) p P := MemLp.of_bound
    (Lp.memLp V).aestronglyMeasurable C
    (by simpa only [Real.norm_eq_abs] using conditional_L2_bound P (G n) (hle n) U C hb)
  obtain ⟨g,hgc,hgd,_,hge⟩ := smooth_cylinder_Lp_approximation P (X n) (hX n) f hf
    p hpt hp (hVi.ae_eq hVf) (ε/2) (half_pos hε)
  refine ⟨n,g,hgc,hgd,?_⟩
  have hv : eLpNorm (fun w => V w-g (X n w)) p P ≤ ENNReal.ofReal (ε/2) := by
    have heq : eLpNorm (fun w => V w-g (X n w)) p P =
        eLpNorm (fun w => f (X n w)-g (X n w)) p P := by
      apply eLpNorm_congr_ae
      filter_upwards [hVf] with w hw
      rw [hw]; rfl
    rw [heq]
    exact hge
  have hu : eLpNorm (fun w => U w-V w) p P < ENNReal.ofReal (ε/2) := by
    rw [show (fun w => U w-V w) = (U : Ω → ℝ)-(V : Ω → ℝ) from rfl,
      eLpNorm_sub_comm]
    exact hn
  calc
    eLpNorm (fun w => U w-g (X n w)) p P =
      eLpNorm ((fun w => U w-V w)+(fun w => V w-g (X n w))) p P := by
        congr 1; funext w; simp
    _ ≤ eLpNorm (fun w => U w-V w) p P + eLpNorm (fun w => V w-g (X n w)) p P := eLpNorm_add_le hp
    _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv) hu hv
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring

end Asakura.Chapter12
