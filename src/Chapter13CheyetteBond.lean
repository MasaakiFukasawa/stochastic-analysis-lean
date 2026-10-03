import Chapter13PrimitiveProducts
import Chapter13BondAlgebra

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- Integrating the Cheyette forward curve gives the bond exponent. -/
theorem cheyette_bond_integral {n:ℕ} (g:Fin n → ℝ → ℝ) (G:Fin n → ℝ → ℝ)
    (f0:ℝ → ℝ) (Y:Fin n → Fin n → ℝ) (X:Fin n → ℝ) (t T:ℝ)
    (hf:IntervalIntegrable f0 volume t T)
    (hg:∀i,IntervalIntegrable (g i) volume t T)
    (hG:∀i,ContinuousOn (G i) (uIcc t T))
    (hprimitive:∀i,∫s in t..T,g i s=G i T-G i t) :
    (∫s in t..T,f0 s+(∑i,∑j,g i s*Y i j*(G j s-G j t))+(∑i,g i s*X i))=
      (∫s in t..T,f0 s)+(∫s in t..T,∑i,∑j,g i s*Y i j*(G j s-G j t))+
      ∑i,(G i T-G i t)*X i := by
  have hij i j:IntervalIntegrable (fun s => g i s*Y i j*(G j s-G j t)) volume t T :=
    ((hg i).mul_const (Y i j)).mul_continuousOn ((hG j).sub continuousOn_const)
  have hi i:IntervalIntegrable (fun s => ∑j,g i s*Y i j*(G j s-G j t)) volume t T := by
    simpa only [Finset.sum_fn,Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun j _ => hij i j)
  have hquad:IntervalIntegrable (fun s => ∑i,∑j,g i s*Y i j*(G j s-G j t)) volume t T := by
    simpa only [Finset.sum_fn,Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  have hlin:IntervalIntegrable (fun s => ∑i,g i s*X i) volume t T := by
    simpa only [Finset.sum_fn,Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => (hg i).mul_const (X i))
  rw [intervalIntegral.integral_add (hf.add hquad) hlin,intervalIntegral.integral_add hf hquad]
  congr 1
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hg i).mul_const (X i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_mul_const,hprimitive]

theorem scalar_cheyette_bond_integral (g:ℝ → ℝ) (t T Y:ℝ)
    (hg:IntervalIntegrable g volume t T) :
    (∫s in t..T,g s*Y*(∫v in t..s,g v))=(∫s in t..T,g s)^2*Y/2 := by
  have he:(fun s => g s*Y*(∫v in t..s,g v))=(fun s => (g s*(∫v in t..s,g v))*Y) := by funext s;ring
  rw [he,intervalIntegral.integral_mul_const,primitive_square_integral g t T hg]
  ring

theorem bond_exponential_ratio (a b c:ℝ) : Real.exp (-(a-b)-c)=Real.exp (-a)/Real.exp (-b)*Real.exp (-c) := by
  rw [←Real.exp_sub,←Real.exp_add]
  congr 1
  ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cheyette_bond_integral
#print axioms Asakura.Chapter13.scalar_cheyette_bond_integral
#print axioms Asakura.Chapter13.bond_exponential_ratio
