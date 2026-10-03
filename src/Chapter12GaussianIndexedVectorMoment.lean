import Chapter12GaussianVectorMoment

open MeasureTheory ProbabilityTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The finite K-valued bound allows tensor-coordinate index sets directly. -/
theorem indexed_vector_divergence_even_moment {n : ℕ} {I : Type*} [Fintype I]
    (u : I → Fin (n+1) → GaussianJet (n+1)) (p : ℕ) (hp : 0<p) :
    (∫ x,gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) x^(2*p)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
    (2*(2*p-1):ℕ)^(2*p) *
      (∫ x,(∑ j : Fin (2*p+1),gaussianArrayNorm
        (fun ab : I × (Fin (j.val+1) → Fin (n+1)) => gaussianDerivativeArray (u ab.1) j ab.2) x)^(2*p)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
  classical
  let e := Fintype.equivFin I
  have hh := actual_vector_divergence_even_moment (fun a => u (e.symm a)) p hp
  have hleft (x : Fin (n+1) → ℝ) :
      gaussianArrayNorm (fun a => GaussianJet.divergence (u (e.symm a))) x=
      gaussianArrayNorm (fun a => GaussianJet.divergence (u a)) x := by
    unfold gaussianArrayNorm
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (GaussianJet.divergence (u a)).f x^2)
  have hright (j : ℕ) (x : Fin (n+1) → ℝ) :
      gaussianVectorDerivativeNorm (fun a => u (e.symm a)) j x=
      gaussianArrayNorm (fun ab : I × (Fin (j+1) → Fin (n+1)) => gaussianDerivativeArray (u ab.1) j ab.2) x := by
    unfold gaussianVectorDerivativeNorm gaussianArrayNorm
    congr 1
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    exact Equiv.sum_comp e.symm (fun a => ∑ b : Fin (j+1) → Fin (n+1),(gaussianDerivativeArray (u a) j b).f x^2)
  simpa only [hleft,gaussianVectorSobolevSum,hright] using hh

end Asakura.Chapter12
