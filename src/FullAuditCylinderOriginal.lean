import FullAuditCommonOrthonormal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Gaussian IBP for the original, possibly dependent cylindrical directions.
 The inputs about W are precisely finite linearity and the joint Gaussian law
 of deterministic Wiener integrals. A common orthonormal system and every
 coordinate transformation in the written proof are constructed here. -/
theorem cylindrical_gaussian_ibp_original {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) (W : H → Ω → ℝ)
    (hlinear : ∀ (l : ℕ) (v : Fin l → H) (c : Fin l → ℝ),
      W (∑ i, c i • v i) =ᵐ[P] fun ω => ∑ i, c i * W (v i) ω)
    (hnormal : ∀ (n : ℕ) (e : Fin (n+1) → H), Orthonormal ℝ e →
      HasLaw (fun ω i => W (e i) ω) (Measure.pi fun _ => gaussianReal 0 1) P)
    {m k : ℕ} (u : Fin m → H) (v : Fin k → H) (h : H)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (hmdf : ∀ j, Measurable (fun x => Df x (Pi.single j 1)))
    (hmdg : ∀ j, Measurable (fun x => Dg x (Pi.single j 1)))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ j, PolyGrowth (fun x => Df x (Pi.single j 1)))
    (hpdg : ∀ j, PolyGrowth (fun x => Dg x (Pi.single j 1))) :
    (∫ ω, g (fun j => W (v j) ω) *
      ⟪∑ j, Df (fun j => W (u j) ω) (Pi.single j 1) • u j, h⟫ ∂P) =
    ∫ ω, f (fun j => W (u j) ω) * (g (fun j => W (v j) ω) * W h ω -
      ⟪∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j, h⟫) ∂P := by
  classical
  let dirs : Fin m ⊕ (Fin k ⊕ Unit) → H := Sum.elim u (Sum.elim v (fun _ => h))
  obtain ⟨n,e,c,he,hc⟩ := finite_common_orthonormal dirs
  let a := c (Sum.inr (Sum.inr ()))
  let cu := fun j => c (Sum.inl j)
  let cv := fun j => c (Sum.inr (Sum.inl j))
  have hu (j : Fin m) : u j = ∑ i, cu j i • e i := hc (Sum.inl j)
  have hv (j : Fin k) : v j = ∑ i, cv j i • e i := hc (Sum.inr (Sum.inl j))
  have hh : h = ∑ i, a i • e i := hc (Sum.inr (Sum.inr ()))
  let Z := fun ω i => W (e i) ω
  let A := cylinderCoordinateMap cu
  let B := cylinderCoordinateMap cv
  have hWh : W h =ᵐ[P] fun ω => ∑ i, a i*Z ω i := by
    rw [hh]
    exact hlinear (n+1) e a
  have hWu (j : Fin m) : W (u j) =ᵐ[P] fun ω => A (Z ω) j := by
    rw [hu]
    simpa only [A,cylinder_coordinate_map_apply] using hlinear (n+1) e (cu j)
  have hWv (j : Fin k) : W (v j) =ᵐ[P] fun ω => B (Z ω) j := by
    rw [hv]
    simpa only [B,cylinder_coordinate_map_apply] using hlinear (n+1) e (cv j)
  have hWus : ∀ᵐ ω ∂P, (fun j => W (u j) ω) = A (Z ω) := by
    filter_upwards [ae_all_iff.mpr hWu] with ω hω
    exact funext hω
  have hWvs : ∀ᵐ ω ∂P, (fun j => W (v j) ω) = B (Z ω) := by
    filter_upwards [ae_all_iff.mpr hWv] with ω hω
    exact funext hω
  have hdu (j : Fin m) : cylindricalDirections e A j = u j := by
    rw [cylindrical_directions_from_coordinates]
    exact (hu j).symm
  have hdv (j : Fin k) : cylindricalDirections e B j = v j := by
    rw [cylindrical_directions_from_coordinates]
    exact (hv j).symm
  have hresult := cylindrical_gaussian_ibp_rebased P e he Z (hnormal n e he) a (W h) hWh
    A B f g Df Dg hf hg hmdf hmdg hpf hpg hpdf hpdg
  simp_rw [hdu,hdv,← hh] at hresult
  have hl : (fun ω => g (fun j => W (v j) ω) *
      ⟪∑ j, Df (fun j => W (u j) ω) (Pi.single j 1) • u j,h⟫) =ᵐ[P]
      (fun ω => g (B (Z ω)) * ⟪∑ j, Df (A (Z ω)) (Pi.single j 1) • u j,h⟫) := by
    filter_upwards [hWus,hWvs] with ω hU hV
    rw [hU,hV]
  have hr : (fun ω => f (fun j => W (u j) ω) *
      (g (fun j => W (v j) ω) * W h ω -
      ⟪∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j,h⟫)) =ᵐ[P]
      (fun ω => f (A (Z ω)) * (g (B (Z ω))*W h ω -
      ⟪∑ j, Dg (B (Z ω)) (Pi.single j 1) • v j,h⟫)) := by
    filter_upwards [hWus,hWvs] with ω hU hV
    rw [hU,hV]
  rw [integral_congr_ae hl,integral_congr_ae hr]
  exact hresult

theorem cylindrical_gaussian_ibp_all_dimensions {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H → Ω → ℝ)
    (hlinear : ∀ (l : ℕ) (v : Fin l → H) (c : Fin l → ℝ),
      W (∑ i, c i • v i) =ᵐ[P] fun ω => ∑ i, c i * W (v i) ω)
    (hnormal : ∀ (n : ℕ) (e : Fin (n+1) → H), Orthonormal ℝ e →
      HasLaw (fun ω i => W (e i) ω) (Measure.pi fun _ => gaussianReal 0 1) P)
    {m k : ℕ} (u : Fin m → H) (v : Fin k → H) (h : H)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
    (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
    (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ)
    (hf : ∀ x, HasFDerivAt f (Df x) x) (hg : ∀ x, HasFDerivAt g (Dg x) x)
    (hmdf : ∀ j, Measurable (fun x => Df x (Pi.single j 1)))
    (hmdg : ∀ j, Measurable (fun x => Dg x (Pi.single j 1)))
    (hpf : PolyGrowth f) (hpg : PolyGrowth g)
    (hpdf : ∀ j, PolyGrowth (fun x => Df x (Pi.single j 1)))
    (hpdg : ∀ j, PolyGrowth (fun x => Dg x (Pi.single j 1))) :
    (∫ ω, g (fun j => W (v j) ω) *
      ⟪∑ j, Df (fun j => W (u j) ω) (Pi.single j 1) • u j, h⟫ ∂P) =
    ∫ ω, f (fun j => W (u j) ω) * (g (fun j => W (v j) ω) * W h ω -
      ⟪∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j, h⟫) ∂P := by
  classical
  cases subsingleton_or_nontrivial H with
  | inr hn =>
    letI := hn
    exact cylindrical_gaussian_ibp_original P W hlinear hnormal u v h f g Df Dg
      hf hg hmdf hmdg hpf hpg hpdf hpdg
  | inl hs =>
    letI := hs
    have hh : h = 0 := Subsingleton.elim _ _
    have hW0 : W (0:H) =ᵐ[P] fun _ => (0:ℝ) := by
      simpa using hlinear 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hzero : (fun ω => f (fun j => W (u j) ω) *
      (g (fun j => W (v j) ω) * W h ω -
      ⟪∑ j, Dg (fun j => W (v j) ω) (Pi.single j 1) • v j,h⟫)) =ᵐ[P] fun _ => (0:ℝ) := by
      filter_upwards [hW0] with ω hω
      simp [hh,hω]
    rw [integral_congr_ae hzero]
    simp [hh]

end Asakura.FullAudit
