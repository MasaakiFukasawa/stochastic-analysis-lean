import Chapter12CubeAverageSum
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Restricting independent uniform coordinates along an injection keeps
the uniform product law, including empty sets of coordinates. -/
theorem finiteMean_coordinate_projection {A B D : Type*}
    [Fintype A] [Fintype B] [Fintype D] [Nonempty D] [DecidableEq A] [DecidableEq B]
    (i : A → B) (hi : Function.Injective i) (φ : (A → D) → ℝ) :
    finiteMean (fun a : B → D => φ (a ∘ i))=finiteMean φ := by
  classical
  let C := {b : B // b∉Set.range i}
  let e : A ⊕ C ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective i hi) (Equiv.refl C)).trans (Equiv.Set.sumCompl (Set.range i))
  let k : (B → D) ≃ (A → D) × (C → D) :=
    (Equiv.arrowCongr e.symm (Equiv.refl D)).trans (Equiv.sumArrowEquivProdArrow A C D)
  have hei (x : A) : e (Sum.inl x)=i x := by
    change (Equiv.Set.sumCompl (Set.range i)) (Sum.inl ((Equiv.ofInjective i hi) x))=i x
    rw [Equiv.Set.sumCompl_apply_inl]
    rfl
  have hk (a : B → D) : (k a).1=a ∘ i := by
    funext x
    change a (e (Sum.inl x))=a (i x)
    rw [hei]
  calc
    _=finiteMean (fun a : B → D => φ ((k a).1)) := by simp only [hk]
    _=finiteMean (fun ab : (A → D) × (C → D) => φ ab.1) := finiteMean_equiv k (fun ab : (A → D) × (C → D) => φ ab.1)
    _=finiteMean φ := finiteMean_prod_fst φ

theorem cubeAverage_coordinate_projection (N e k : ℕ)
    (i : Fin k → Fin e) (hi : Function.Injective i) (φ : (Fin k → Fin (N+1)) → ℝ) :
    cubeAverage N e (fun a => φ (a ∘ i))=cubeAverage N k φ := by
  rw [cubeAverage_eq_finiteMean,cubeAverage_eq_finiteMean]
  exact finiteMean_coordinate_projection i hi φ

end Asakura.Chapter12
