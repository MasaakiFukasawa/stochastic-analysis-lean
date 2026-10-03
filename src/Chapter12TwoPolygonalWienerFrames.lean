import Chapter12WienerPolygonalFrame

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem two_polygonal_wiener_frames {Ω H I : Type*} [MeasurableSpace Ω] [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (f : I → ℝ → H) (X : I → ℝ → Ω → ℝ) (h h' : ℝ) (n n' : ℕ)
    (hX : ∀i (j : Fin (n+1)),X i ((j:ℝ)*h)=ᵐ[P] (W (f i ((j:ℝ)*h)) : Ω → ℝ))
    (hX' : ∀i (j : Fin (n'+1)),X i ((j:ℝ)*h')=ᵐ[P] (W (f i ((j:ℝ)*h')) : Ω → ℝ)) :
    ∃m:ℕ,∃e:Fin (m+1) → H,Orthonormal ℝ e ∧
      (∀i t,polygonalPath (f i) h n t=∑j,inner ℝ (e j) (polygonalPath (f i) h n t) • e j) ∧
      (∀i t,polygonalPath (f i) h' n' t=∑j,inner ℝ (e j) (polygonalPath (f i) h' n' t) • e j) ∧
      (∀ᵐw ∂P,∀i t,polygonalPath (fun s => X i s w) h n t=
        ∑j,inner ℝ (e j) (polygonalPath (f i) h n t)*W (e j) w) ∧
      (∀ᵐw ∂P,∀i t,polygonalPath (fun s => X i s w) h' n' t=
        ∑j,inner ℝ (e j) (polygonalPath (f i) h' n' t)*W (e j) w) := by
  classical
  let dirs : (I × Fin (n+1)) ⊕ (I × Fin (n'+1)) → H :=
    Sum.elim (fun ij => f ij.1 ((ij.2:ℝ)*h)) (fun ij => f ij.1 ((ij.2:ℝ)*h'))
  obtain ⟨m,e,c,he,hc⟩ := finite_common_orthonormal dirs
  let c₁ := fun i (j : Fin (n+1)) => c (Sum.inl (i,j))
  let c₂ := fun i (j : Fin (n'+1)) => c (Sum.inr (i,j))
  have hc₁ (i : I) (j : Fin (n+1)) : f i ((j:ℝ)*h)=∑a,c₁ i j a • e a := hc (Sum.inl (i,j))
  have hc₂ (i : I) (j : Fin (n'+1)) : f i ((j:ℝ)*h')=∑a,c₂ i j a • e a := hc (Sum.inr (i,j))
  refine ⟨m,e,he,?_,?_,?_,?_⟩
  · exact fun i t => polygonal_orthonormal_representation e he (f i) h n (c₁ i) (hc₁ i) t
  · exact fun i t => polygonal_orthonormal_representation e he (f i) h' n' (c₂ i) (hc₂ i) t
  · exact ae_all_iff.mpr (fun i => wiener_polygonal_frame P W (m+1) e he (f i) (X i) h n (c₁ i) (hc₁ i) (hX i))
  · exact ae_all_iff.mpr (fun i => wiener_polygonal_frame P W (m+1) e he (f i) (X i) h' n' (c₂ i) (hc₂ i) (hX' i))
end Asakura.Chapter12
#print axioms Asakura.Chapter12.two_polygonal_wiener_frames
