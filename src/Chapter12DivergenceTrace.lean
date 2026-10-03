import Chapter12Representation

open MeasureTheory
namespace Asakura.Chapter12
set_option maxHeartbeats 600000

/-- No positivity of the trace term is assumed. The transpose pairing is
bounded in absolute value by the squared Hilbert--Schmidt norm. -/
theorem transpose_pairing_bound {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) :
    |∑ i, ∑ j, A i j * A j i| ≤ ∑ i, ∑ j, (A i j)^2 := by
  classical
  apply abs_le.mpr
  have hup : (∑ i, ∑ j, A i j*A j i) ≤
      ∑ i, ∑ j, ((A i j)^2+(A j i)^2)/2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (A i j-A j i)]
  have hlo : -(∑ i, ∑ j, ((A i j)^2+(A j i)^2)/2) ≤
      ∑ i, ∑ j, A i j*A j i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (A i j+A j i)]
  have he : (∑ i, ∑ j, ((A i j)^2+(A j i)^2)/2) =
      ∑ i, ∑ j, (A i j)^2 := by
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => (A j i)^2)]
    ring
  exact ⟨by simpa only [he] using hlo, by simpa only [he] using hup⟩

/-- The last step of the cylindrical divergence estimate, applied pointwise
before integration. Integrability of the trace is obtained from domination. -/
theorem integrated_transpose_pairing_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) (A : Ω → ι → ι → ℝ)
    (hm : ∀ i j, AEStronglyMeasurable (fun ω => A ω i j) P)
    (hi : Integrable (fun ω => ∑ i, ∑ j, (A ω i j)^2) P) :
    Integrable (fun ω => ∑ i, ∑ j, A ω i j*A ω j i) P ∧
    |∫ ω, ∑ i, ∑ j, A ω i j*A ω j i ∂P| ≤
      ∫ ω, ∑ i, ∑ j, (A ω i j)^2 ∂P := by
  have hm' : AEStronglyMeasurable (fun ω => ∑ i, ∑ j, A ω i j*A ω j i) P :=
    by
      convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
          Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => (hm i j).mul (hm j i))) using 1
      ext ω
      simp only [Finset.sum_apply,Pi.mul_apply]
  have hb : ∀ᵐ ω ∂P, ‖∑ i, ∑ j, A ω i j*A ω j i‖ ≤
      ∑ i, ∑ j, (A ω i j)^2 :=
    ae_of_all P fun ω => transpose_pairing_bound (A ω)
  refine ⟨hi.mono' hm' hb, ?_⟩
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae (hi.mono' hm' hb).norm hi hb)

end Asakura.Chapter12
