import Chapter12DivergencePowerIBP

open MeasureTheory ProbabilityTheory Finset
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem polynomial_growth_finset_prod {E ι : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → E → ℝ) (hf : ∀ j∈s,PolyGrowth (f j)) :
    PolyGrowth (fun x => ∏ j∈s,f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowth.const (E := E) 1
  | @insert a s ha ih =>
    simpa only [Finset.prod_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- One complete step of the high-moment iteration: removing a selected
finite Gaussian divergence differentiates precisely one other factor.
All integrability is obtained from polynomial growth. -/
theorem gaussian_divergence_product_ibp {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (f : J → (Fin (n+1) → ℝ) → ℝ)
    (df : J → Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (u du : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ j i z y,HasDerivAt (fun x => f j (i.insertNth x z)) (df j i (i.insertNth y z)) y)
    (hu : ∀ i z y,HasDerivAt (fun x => u i (i.insertNth x z)) (du i (i.insertNth y z)) y)
    (hmf : ∀ j,Measurable (f j)) (hpf : ∀ j,PolyGrowth (f j))
    (hmdf : ∀ j i,Measurable (df j i)) (hpdf : ∀ j i,PolyGrowth (df j i))
    (hmu : ∀ i,Measurable (u i)) (hpu : ∀ i,PolyGrowth (u i))
    (hmdu : ∀ i,Measurable (du i)) (hpdu : ∀ i,PolyGrowth (du i)) :
    (∫ z : Fin (n+1) → ℝ,(∏ j,f j z)*(∑ i : Fin (n+1), (z i * u i z - du i z))
      ∂Measure.pi fun _ => gaussianReal 0 1)=
    ∑ j : J,∫ z : Fin (n+1) → ℝ,(∏ l∈Finset.univ.erase j,f l z)*(∑ i,u i z*df j i z)
      ∂Measure.pi fun _ => gaussianReal 0 1 := by
  classical
  have hprod (s : Finset J) : PolyGrowth (fun z => ∏ j∈s,f j z) :=
    polynomial_growth_finset_prod s f (fun j _ => hpf j)
  have hder (i z y) := HasDerivAt.fun_finsetProd
    (u := Finset.univ) (fun j _ => hf j i z y)
  have hh := finite_gaussian_divergence_duality (fun z => ∏ j,f j z)
    (fun i z => ∑ j,(∏ l∈Finset.univ.erase j,f l z)*df j i z) u du
    (fun i z y => by simpa only [smul_eq_mul] using hder i z y) hu
    (by fun_prop) (hprod Finset.univ) (fun i => by fun_prop)
    (fun i => PolyGrowth.finset_sum _ _ (fun j _ => (hprod _).mul (hpdf j i)))
    hmu hpu hmdu hpdu
  rw [← hh]
  have hi (j : J) : Integrable (fun z => (∏ l∈Finset.univ.erase j,f l z)*(∑ i,u i z*df j i z))
      (Measure.pi fun _ => gaussianReal 0 1) :=
    polynomial_growth_gaussian_integrable (by fun_prop)
      ((hprod _).mul (PolyGrowth.finset_sum _ _ (fun i _ => (hpu i).mul (hpdf j i))))
  rw [← integral_finset_sum _ (fun j _ => hi j)]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Asakura.Chapter12
