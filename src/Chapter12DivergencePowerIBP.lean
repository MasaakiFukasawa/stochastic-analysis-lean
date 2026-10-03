import Chapter12GaussianGrowth

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem polynomial_growth_pow {E : Type*} [SeminormedAddCommGroup E]
    {f : E → ℝ} (hf : PolyGrowth f) (k : ℕ) : PolyGrowth (fun x => f x^k) := by
  induction k with
  | zero => simpa only [pow_zero] using PolyGrowth.const (E := E) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

/-- The first high-moment integration by parts is checked with the actual
coordinate derivatives and polynomial integrability. k = 2p-1 is the
formula printed in the manuscript. -/
theorem finite_divergence_power_ibp {n : ℕ}
    (u : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (du : Fin (n+1) → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (dV : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hu : ∀ i z y, HasDerivAt (fun x => u i (i.insertNth x z))
      (du i i (i.insertNth y z)) y)
    (hV : ∀ i z y, HasDerivAt (fun x => gaussianDivergence u du (i.insertNth x z))
      (dV i (i.insertNth y z)) y)
    (hmu : ∀ i, Measurable (u i)) (hpu : ∀ i, PolyGrowth (u i))
    (hmdu : ∀ i j, Measurable (du i j)) (hpdu : ∀ i j, PolyGrowth (du i j))
    (hmdV : ∀ i, Measurable (dV i)) (hpdV : ∀ i, PolyGrowth (dV i)) (k : ℕ) :
    (∫ z, gaussianDivergence u du z^(k+1) ∂Measure.pi fun _ => gaussianReal 0 1) =
      (k:ℝ)*(∫ z, gaussianDivergence u du z^(k-1)*(∑ i,u i z*dV i z)
        ∂Measure.pi fun _ => gaussianReal 0 1) := by
  let V := gaussianDivergence u du
  have hmV : Measurable V := gaussian_divergence_measurable u du hmu hmdu
  have hpV : PolyGrowth V := gaussian_divergence_growth u du hpu hpdu
  have hh := finite_gaussian_divergence_duality (fun z => V z^k)
    (fun i z => (k:ℝ)*V z^(k-1)*dV i z) u (fun i => du i i)
    (fun i z y => (hV i z y).pow k) hu (hmV.pow_const k) (polynomial_growth_pow hpV k)
    (fun i => ((hmV.pow_const (k-1)).const_mul k).mul (hmdV i))
    (fun i => ((PolyGrowth.const (k:ℝ)).mul (polynomial_growth_pow hpV (k-1))).mul (hpdV i))
    hmu hpu (fun i => hmdu i i) (fun i => hpdu i i)
  have he : (∫ z, V z^(k+1) ∂Measure.pi fun _ => gaussianReal 0 1) =
      ∫ z, ∑ i,u i z*((k:ℝ)*V z^(k-1)*dV i z) ∂Measure.pi fun _ => gaussianReal 0 1 := by
    simpa only [V,gaussianDivergence,pow_succ] using hh.symm
  rw [he,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Asakura.Chapter12
