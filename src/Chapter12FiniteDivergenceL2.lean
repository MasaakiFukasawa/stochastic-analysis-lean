import Chapter12GaussianGrowth

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The two Gaussian integrations by parts in the manuscript, including
all finite sums and integrability. This is an identity, before discarding
the potentially negative transpose term. -/
theorem finite_divergence_square_identity {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (ddu : Fin (n+1) → Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hu : ∀ i j z y, HasDerivAt (fun x => u j (i.insertNth x z))
      (du i j (i.insertNth y z)) y)
    (hdu : ∀ i j k z y, HasDerivAt (fun x => du j k (i.insertNth x z))
      (ddu i j k (i.insertNth y z)) y)
    (hsym : ∀ i j k z, ddu i j k z = ddu j i k z)
    (hmu : ∀ i, Measurable (u i)) (hpu : ∀ i, PolyGrowth (u i))
    (hmdu : ∀ i j, Measurable (du i j)) (hpdu : ∀ i j, PolyGrowth (du i j))
    (hmdd : ∀ i j k, Measurable (ddu i j k))
    (hpdd : ∀ i j k, PolyGrowth (ddu i j k)) :
    (∫ z, (gaussianDivergence u du z)^2 ∂Measure.pi fun _ => gaussianReal 0 1) =
      (∫ z, ∑ i, (u i z)^2 ∂Measure.pi fun _ => gaussianReal 0 1) +
      (∫ z, ∑ i, ∑ j, du i j z*du j i z ∂Measure.pi fun _ => gaussianReal 0 1) := by
  let γ : Measure (Fin (n+1) → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let V := gaussianDivergence u du
  let B := fun i => gaussianDivergence (du i) (fun j k => ddu j i k)
  have hBm i : Measurable (B i) :=
    gaussian_divergence_measurable _ _ (hmdu i) (fun j k => hmdd j i k)
  have hBp i : PolyGrowth (B i) :=
    gaussian_divergence_growth _ _ (hpdu i) (fun j k => hpdd j i k)
  have hi1 i : Integrable (fun z => (u i z)^2) γ := by
    convert polynomial_growth_gaussian_integrable
      ((hmu i).mul (hmu i)) ((hpu i).mul (hpu i)) using 1
    ext z
    simp only [pow_two,Pi.mul_apply]
  have hi2 i : Integrable (fun z => u i z*B i z) γ :=
    polynomial_growth_gaussian_integrable ((hmu i).mul (hBm i)) ((hpu i).mul (hBp i))
  have hi3 i j : Integrable (fun z => du i j z*du j i z) γ :=
    polynomial_growth_gaussian_integrable ((hmdu i j).mul (hmdu j i))
      ((hpdu i j).mul (hpdu j i))
  have hfirst := finite_gaussian_divergence_duality V (fun i z => u i z+B i z)
    u (fun i => du i i) (finite_divergence_commutation u du ddu hu hdu hsym)
    (fun i => hu i i) (gaussian_divergence_measurable u du hmu hmdu)
    (gaussian_divergence_growth u du hpu hpdu)
    (fun i => (hmu i).add (hBm i)) (fun i => (hpu i).add (hBp i))
    hmu hpu (fun i => hmdu i i) (fun i => hpdu i i)
  have hsecond i := finite_gaussian_divergence_duality (u i) (fun j => du j i)
    (du i) (fun j => ddu j i j) (fun j => hu j i) (fun j => hdu j i j)
    (hmu i) (hpu i) (fun j => hmdu j i) (fun j => hpdu j i)
    (hmdu i) (hpdu i) (fun j => hmdd j i j) (fun j => hpdd j i j)
  change (∫ z, V z^2 ∂γ) = _
  have he : (∫ z, ∑ i, u i z*(u i z+B i z) ∂γ) = ∫ z,V z^2 ∂γ := by
    simpa only [V,gaussianDivergence,pow_two] using hfirst
  rw [← he]
  have hp (z : Fin (n+1) → ℝ) : (∑ i,u i z*(u i z+B i z)) =
      (∑ i,(u i z)^2)+(∑ i,u i z*B i z) := by
    simp only [mul_add,Finset.sum_add_distrib,pow_two]
  simp_rw [hp]
  rw [integral_add (integrable_finset_sum _ (fun i _ => hi1 i))
    (integrable_finset_sum _ (fun i _ => hi2 i))]
  congr 1
  rw [integral_finset_sum _ (fun i _ => hi2 i),
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi3 i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (hsecond i).symm

theorem finite_divergence_l2_bound {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (ddu : Fin (n+1) → Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hu : ∀ i j z y, HasDerivAt (fun x => u j (i.insertNth x z))
      (du i j (i.insertNth y z)) y)
    (hdu : ∀ i j k z y, HasDerivAt (fun x => du j k (i.insertNth x z))
      (ddu i j k (i.insertNth y z)) y)
    (hsym : ∀ i j k z, ddu i j k z = ddu j i k z)
    (hmu : ∀ i, Measurable (u i)) (hpu : ∀ i, PolyGrowth (u i))
    (hmdu : ∀ i j, Measurable (du i j)) (hpdu : ∀ i j, PolyGrowth (du i j))
    (hmdd : ∀ i j k, Measurable (ddu i j k))
    (hpdd : ∀ i j k, PolyGrowth (ddu i j k)) :
    (∫ z, (gaussianDivergence u du z)^2 ∂Measure.pi fun _ => gaussianReal 0 1) ≤
      (∫ z, ∑ i, (u i z)^2 ∂Measure.pi fun _ => gaussianReal 0 1) +
      (∫ z, ∑ i, ∑ j, (du i j z)^2 ∂Measure.pi fun _ => gaussianReal 0 1) := by
  have hi i j : Integrable (fun z => (du i j z)^2)
      (Measure.pi fun _ => gaussianReal 0 1) := by
    convert polynomial_growth_gaussian_integrable
      ((hmdu i j).mul (hmdu i j)) ((hpdu i j).mul (hpdu i j)) using 1
    ext z
    simp only [pow_two,Pi.mul_apply]
  have his : Integrable (fun z => ∑ i, ∑ j, (du i j z)^2)
      (Measure.pi fun _ => gaussianReal 0 1) :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hi i j))
  have hb := integrated_transpose_pairing_bound
    (Measure.pi fun _ => gaussianReal 0 1) (fun z i j => du i j z)
    (fun i j => (hmdu i j).aestronglyMeasurable) his
  rw [finite_divergence_square_identity u du ddu hu hdu hsym hmu hpu hmdu hpdu hmdd hpdd]
  exact add_le_add le_rfl ((le_abs_self _).trans hb.2)

end Asakura.Chapter12
