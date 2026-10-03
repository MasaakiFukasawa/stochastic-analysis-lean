import Chapter11WeightedEnergy
import Chapter11PayoffIntegrability

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The merely progressive, possibly unbounded representation integrand
gives a valid stock/bank strategy. Finite-variation integrability follows
from L2 on a finite time interval, not from continuity of the strategy. -/
theorem replication_strategy_path_integrability (φ M S : ℝ → ℝ)
    (hφ : Measurable φ) (hS : ∀ t,0<S t) (T r μ σ : ℝ) (hT : 0≤T) (hσ : σ≠0)
    (hi : Integrable (fun t => (φ t)^2) (volume.restrict (Ioc 0 T)))
    (hM : ContinuousOn M (Icc 0 T)) :
    let H := fun t => φ t/(σ*(Real.exp (-r*t)*S t))
    let η := fun t => M t-φ t/σ
    (∀ t,H t*S t+η t*Real.exp (r*t)=Real.exp (r*t)*M t) ∧
      Integrable (fun t => H t*(μ*S t)) (volume.restrict (Ioc 0 T)) ∧
      Integrable (fun t => (H t*(σ*S t))^2) (volume.restrict (Ioc 0 T)) ∧
      Integrable (fun t => η t*(r*Real.exp (r*t))) (volume.restrict (Ioc 0 T)) ∧
      (∀ t,(H t)^2*σ^2*(Real.exp (-r*t)*S t)^2=(φ t)^2) := by
  dsimp only
  have hE t : Real.exp (-r*t)*Real.exp (r*t)=1 := by rw [←Real.exp_add];convert Real.exp_zero using 2 <;> ring
  have hA t : φ t/(σ*(Real.exp (-r*t)*S t))*S t=Real.exp (r*t)*φ t/σ := by
    have hS0 := (hS t).ne'
    have he0 := (Real.exp_pos (-r*t)).ne'
    field_simp
    have he := hE t
    simp only [neg_mul] at he
    rw [mul_assoc,he,mul_one]
  have hN t : φ t/(σ*(Real.exp (-r*t)*S t))*(σ*S t)=Real.exp (r*t)*φ t := by
    calc
      _ = σ*(φ t/(σ*(Real.exp (-r*t)*S t))*S t) := by ring
      _ = _ := by rw [hA];field_simp
  have hL2 : MemLp φ 2 (volume.restrict (Ioc 0 T)) := (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mpr hi
  have hL1 := hL2.integrable (by norm_num : (1:ENNReal)≤2)
  have he : ContinuousOn (fun t : ℝ => Real.exp (r*t)) (Icc 0 T) := by fun_prop
  have hei := continuous_multiplier_integrable T hT _
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => ⟨ht.1.le,ht.2⟩)
    (fun t => Real.exp (r*t)) φ he (by fun_prop) hL1
  have he2i := continuous_multiplier_integrable T hT _
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => ⟨ht.1.le,ht.2⟩)
    (fun t => (Real.exp (r*t))^2) (fun t => (φ t)^2) (he.pow 2) (by fun_prop) hi
  have hm : Integrable (fun t => M t*Real.exp (r*t)) (volume.restrict (Ioc 0 T)) :=
    (hM.mul he).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t
    rw [hA]
    ring
  · have heq : (fun t => φ t/(σ*(Real.exp (-r*t)*S t))*(μ*S t))=(fun t => (μ/σ)*(Real.exp (r*t)*φ t)) := by
      funext t
      calc
        _ = μ*(φ t/(σ*(Real.exp (-r*t)*S t))*S t) := by ring
        _ = _ := by rw [hA];ring
    rw [heq]
    exact hei.const_mul _
  · simp_rw [hN,mul_pow]
    exact he2i
  · have heq : (fun t => (M t-φ t/σ)*(r*Real.exp (r*t)))=
        (fun t => r*(M t*Real.exp (r*t))-(r/σ)*(Real.exp (r*t)*φ t)) := by funext t;ring
    rw [heq]
    exact (hm.const_mul r).sub (hei.const_mul _)
  · intro t
    field_simp [hσ,(hS t).ne',Real.exp_ne_zero]

end Asakura.Chapter11
