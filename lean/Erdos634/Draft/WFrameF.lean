-- Draft/WFrameF.lean — L1 of (private working notes, not included) §3: the skew W-frame for general parameter f.
-- Phi_f(s,t) = s*g1 + t*g2, g1 = (1,0), g2 = (1/(2f), sqrt(4f²-1)/(2f)); |g1|=|g2|=1, g1.g2 = 1/(2f).
-- f = 2 specializes to (1/8)·WFrame.Phi (see `Phi_two_eq`).  UNAUDITED.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.WFrame

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (Sh Tset Rect RTiling.cast)

namespace Erdos634.Draft.WFrameF
open Erdos634.Draft.RegionTiling

/-- `sqrt (4f²-1)`. -/
noncomputable def sD (f : ℝ) : ℝ := Real.sqrt (4 * f ^ 2 - 1)

theorem sD_pos {f : ℝ} (hf : 1 < f) : 0 < sD f := by
  unfold sD; apply Real.sqrt_pos.mpr; nlinarith

theorem sD_sq {f : ℝ} (hf : 1 < f) : sD f ^ 2 = 4 * f ^ 2 - 1 := by
  unfold sD; rw [Real.sq_sqrt]; nlinarith

noncomputable def g1 : Plane := mkPt 1 0
noncomputable def g2 (f : ℝ) : Plane := mkPt (1 / (2 * f)) (sD f / (2 * f))

/-- Skew coordinates → plane. -/
noncomputable def Phi (f : ℝ) (p : ℝ × ℝ) : Plane := p.1 • g1 + p.2 • g2 f

/-- Plane → skew coordinates. -/
noncomputable def Psi (f : ℝ) (q : Plane) : ℝ × ℝ :=
  (q 0 - q 1 / sD f, q 1 * (2 * f) / sD f)

theorem Phi_apply0 (f : ℝ) (p : ℝ × ℝ) : Phi f p 0 = p.1 + p.2 / (2 * f) := by
  simp [Phi, g1, g2, div_eq_mul_inv]

theorem Phi_apply1 (f : ℝ) (p : ℝ × ℝ) : Phi f p 1 = p.2 * (sD f / (2 * f)) := by
  simp [Phi, g1, g2]

theorem Psi_Phi {f : ℝ} (hf : 1 < f) (p : ℝ × ℝ) : Psi f (Phi f p) = p := by
  have h := (sD_pos hf).ne'
  have h2 : f ≠ 0 := by positivity
  ext
  · simp only [Psi, Phi_apply0, Phi_apply1]; field_simp; ring
  · simp only [Psi, Phi_apply1]; field_simp

theorem Phi_Psi {f : ℝ} (hf : 1 < f) (q : Plane) : Phi f (Psi f q) = q := by
  have h := (sD_pos hf).ne'
  have h2 : f ≠ 0 := by positivity
  ext i
  fin_cases i
  · show Phi f (Psi f q) 0 = q 0
    rw [Phi_apply0]; simp only [Psi]; field_simp; ring
  · show Phi f (Psi f q) 1 = q 1
    rw [Phi_apply1]; simp only [Psi]; field_simp

theorem Phi_cont (f : ℝ) : Continuous (Phi f) := by
  unfold Phi; fun_prop

theorem Psi_cont (f : ℝ) : Continuous (Psi f) := by
  unfold Psi
  have h0 : Continuous fun q : Plane => q 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun q : Plane => q 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  fun_prop

/-- The skew coordinate system as a homeomorphism. -/
noncomputable def PhiH {f : ℝ} (hf : 1 < f) : (ℝ × ℝ) ≃ₜ Plane where
  toFun := Phi f
  invFun := Psi f
  left_inv := Psi_Phi hf
  right_inv := Phi_Psi hf
  continuous_toFun := Phi_cont f
  continuous_invFun := Psi_cont f

theorem interior_image {f : ℝ} (hf : 1 < f) (S : Set (ℝ × ℝ)) :
    interior (Phi f '' S) = Phi f '' interior S :=
  ((PhiH hf).image_interior S).symm

theorem disjoint_image {f : ℝ} (hf : 1 < f) {A B : Set (ℝ × ℝ)}
    (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (Phi f '' A)) (interior (Phi f '' B)) := by
  rw [interior_image hf, interior_image hf]
  exact (Set.disjoint_image_iff (PhiH hf).injective).mpr h

theorem Phi_add (f : ℝ) (p q : ℝ × ℝ) : Phi f (p + q) = Phi f p + Phi f q := by
  unfold Phi; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel

theorem image_shift (f : ℝ) (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    (fun x : Plane => x + Phi f v) '' (Phi f '' S) = Phi f '' Sh v S := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p + v, ?_, by rw [Phi_add]⟩
    show p + v - v ∈ S; simpa using hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Phi f (p - v), ⟨p - v, hp, rfl⟩, ?_⟩
    show Phi f (p - v) + Phi f v = Phi f p
    rw [← Phi_add]; simp

noncomputable def shiftR {f : ℝ} {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ}
    (R : RTiling (Phi f '' S) M N) (v : ℝ × ℝ) : RTiling (Phi f '' Sh v S) M N :=
  RTiling.cast (image_shift f v S)
    (Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight (Phi f v)))

/-- **L1.** `|Φ(Δs,Δt)|² = Δs² + Δt² + Δs·Δt/f`. -/
theorem sq_Phi {f : ℝ} (hf : 1 < f) (a b : ℝ × ℝ) :
    dist (Phi f a) (Phi f b) ^ 2
      = (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2 + (a.1 - b.1) * (a.2 - b.2) / f := by
  have e : ∀ c : ℝ × ℝ, Phi f c = mkPt (c.1 + c.2 / (2 * f)) (c.2 * (sD f / (2 * f))) :=
    fun c => by ext i; fin_cases i <;> simp [Phi_apply0, Phi_apply1]
  rw [e a, e b, dist_sq_mkPt]
  have h := sD_sq hf
  have h2 : f ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [h]; ring

/-- Specialization at `f = 2`: `Φ_2 = (1/8)·Φ_{(1,2)}` (the old frame has `g1 = (8,0)`). -/
theorem Phi_two_eq (p : ℝ × ℝ) :
    Phi 2 p = (1 / 8 : ℝ) • Erdos634.Draft.WFrame.Phi p := by
  have h15 : sD 2 = Erdos634.Draft.CollarParam.s15 := by
    unfold sD Erdos634.Draft.CollarParam.s15; norm_num
  ext i; fin_cases i
  · show Phi 2 p 0 = (1 / 8 : ℝ) * Erdos634.Draft.WFrame.Phi p 0
    rw [Phi_apply0, Erdos634.Draft.WFrame.Phi_apply0]; ring
  · show Phi 2 p 1 = (1 / 8 : ℝ) * Erdos634.Draft.WFrame.Phi p 1
    rw [Phi_apply1, Erdos634.Draft.WFrame.Phi_apply1, h15]; ring

end Erdos634.Draft.WFrameF

#print axioms Erdos634.Draft.WFrameF.sq_Phi
#print axioms Erdos634.Draft.WFrameF.shiftR
#print axioms Erdos634.Draft.WFrameF.Phi_two_eq
