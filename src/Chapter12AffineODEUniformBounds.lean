import Chapter12UniformVolterraDerivativeBounds
import Chapter12AffineForcingArray

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem affine_ode_uniform_bounds {E α : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T : ℝ) (hT : 0≤T)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀q t,S q t=q t+∫s in 0..t.val,b (S q (projIcc 0 T hT s)))
    (N : α → ℕ) (a : α → C(Icc (0:ℝ) T,E))
    (L : ∀i,(Fin (N i) → ℝ) →L[ℝ] C(Icc (0:ℝ) T,E))
    (B : ℝ) (hB : 0≤B)
    (hLB : ∀i t,Real.sqrt (∑j,‖L i (Pi.single j 1) t‖^2)≤B) :
    ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀i z t,
      Real.sqrt (∑j : Fin k → Fin (N i),
        ‖(iteratedFDeriv ℝ k (fun y => S (a i+L i y)) z (fun r => Pi.single (j r) 1)) t‖^2)≤C := by
  let Q := fun i (z : Fin (N i) → ℝ) => a i+L i z
  let X := fun i => S ∘ Q i
  have hQ i : ContDiff ℝ ∞ (Q i) := contDiff_const.add (L i).contDiff
  have hX i : ContDiff ℝ ∞ (X i) := hS.comp (hQ i)
  have heq i z t : X i z t=Q i z t+∫s in 0..t.val,b (X i z (projIcc 0 T hT s)) := hSeq (Q i z) t
  have hQB k (hk : 1≤k) i z t :
      Real.sqrt (∑j : Fin k → Fin (N i),‖(iteratedFDeriv ℝ k (Q i) z (fun r => Pi.single (j r) 1)) t‖^2)≤
        (if k=1 then B else 0) := affine_forcing_array_bounds (L i) (a i) B hB (hLB i) k hk z t
  exact uniform_volterra_derivative_bounds (fun i => Fin (N i) → ℝ) (fun i => Fin (N i)) b hb hbound T hT Q X hQ hX heq
    (fun _ j => Pi.single j 1) (fun k => if k=1 then B else 0) (fun k => by split_ifs <;> positivity) hQB
end Asakura.Chapter12
#print axioms Asakura.Chapter12.affine_ode_uniform_bounds
