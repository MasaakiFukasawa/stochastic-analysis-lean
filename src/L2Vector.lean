import L2Moments

open MeasureTheory
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def L2vector (f : ι → Lp ℝ 2 P) : Lp (ι → ℝ) 2 P :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (f i)

lemma L2vector_coe (f : ι → Lp ℝ 2 P) :
    (L2vector f : Ω → ι → ℝ) =ᵐ[P] fun ω i => f i ω := by
  have ha : ∀ᵐ ω ∂P, ∀ i : ι,
      ((ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (f i)) ω =
        Pi.single i (f i ω) :=
    ae_all_iff.mpr (fun i => (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).coeFn_compLp _)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (f i)), ha] with ω h hω
  change (L2vector f : Ω → ι → ℝ) ω = _
  unfold L2vector
  rw [h]
  ext i
  simp only [Finset.sum_apply]
  simp [hω]

lemma L2vector_hasSum (f : ℕ → ι → Lp ℝ 2 P) (g : ι → Lp ℝ 2 P)
    (hf : ∀ i, HasSum (fun n => f n i) (g i)) :
    HasSum (fun n => L2vector (f n)) (L2vector g) := by
  unfold L2vector
  apply hasSum_sum
  intro i hi
  exact (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLpL 2 P |>.hasSum (hf i)
end Asakura
