import Chapter8NewtonEnergy

open Set Finset
open scoped BigOperators
namespace Asakura.Chapter8

/-- For a quadratic potential each eigendirection has l=u. A finite minimum
of the resulting positive rates removes the restriction on positive friction. -/
theorem quadratic_direction_contraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (k : ι → ℝ) (hk : ∀ i, 0 < k i) (δ : ℝ) (hd : 0 < δ) :
    ∃ (b : ι → ℝ) (r : ℝ), 0 < r ∧ (∀ i, 0 < b i+δ^2/4) ∧
      ∀ (q v : ι → ℝ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ i, ContinuousOn (q i) (Icc 0 T)) → (∀ i, ContinuousOn (v i) (Icc 0 T)) →
      (∀ i t, t ∈ Ioo 0 T → HasDerivAt (q i) (v i t) t) →
      (∀ i t, t ∈ Ioo 0 T → HasDerivAt (v i) (-k i*q i t-δ*v i t) t) →
      ∀ t ∈ Icc 0 T,
        (∑ i, newtonEnergy δ (b i) (q i t) (v i t)) ≤
          Real.exp (-2*r*t)*(∑ i, newtonEnergy δ (b i) (q i 0) (v i 0)) := by
  classical
  have hex (i : ι) := scalar_newton_contraction (k i) (k i) δ (hk i) le_rfl (by simpa using hd)
  choose b rates hr hp hpath using hex
  let r := univ.inf' univ_nonempty rates
  have hrpos : 0 < r := (lt_inf'_iff _).mpr (fun i _ => hr i)
  have hri (i : ι) : r ≤ rates i := inf'_le rates (mem_univ i)
  refine ⟨b,r,hrpos,hp,?_⟩
  intro q v T hT hq hv hdq hdv t ht
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hthis := hpath i (q i) (v i) (fun _ => k i) T hT (hq i) (hv i)
    (fun _ _ => ⟨le_rfl,le_rfl⟩) (hdq i) (hdv i) t ht
  have he : Real.exp (-2*rates i*t) ≤ Real.exp (-2*r*t) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr (hri i)) ht.1])
  have hE : 0 ≤ newtonEnergy δ (b i) (q i 0) (v i 0) := by
    by_cases hzero : q i 0 = 0 ∧ v i 0 = 0
    · simp [newtonEnergy,hzero.1,hzero.2]
    · apply le_of_lt (newton_energy_positive δ (b i) (q i 0) (v i 0) (hp i) _)
      simpa only [not_and_or] using hzero
  exact hthis.trans (mul_le_mul_of_nonneg_right he hE)

end Asakura.Chapter8
