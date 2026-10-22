-- Draft/WFrame.lean — skew coordinates for the W-frame of the (1,2) cevian family (7m^2):
-- Phi(s,t) = s*g1 + t*g2, g1 = (8,0) (cevian direction), g2 = (2, 2*sqrt15) (base direction);
-- |g1| = |g2| = 8 and g1.g2 = 16 (cos = 1/4 = cos(alpha+beta)).  Tile (2,3,4) has sides (16,24,32).
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.CollarParam

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (s15 s15_pos s15_sq Sh Tset Rect RTiling.cast)

namespace Erdos634.Draft.WFrame
open Erdos634.Draft.RegionTiling

noncomputable def g1 : Plane := mkPt 8 0
noncomputable def g2 : Plane := mkPt 2 (2 * s15)

/-- Skew coordinates → plane. -/
noncomputable def Phi (p : ℝ × ℝ) : Plane := p.1 • g1 + p.2 • g2

/-- Plane → skew coordinates. -/
noncomputable def Psi (q : Plane) : ℝ × ℝ :=
  ((q 0 - q 1 * (2 / (2 * s15))) / 8, q 1 / (2 * s15))

theorem Phi_apply0 (p : ℝ × ℝ) : Phi p 0 = 8 * p.1 + 2 * p.2 := by
  simp [Phi, g1, g2]; ring

theorem Phi_apply1 (p : ℝ × ℝ) : Phi p 1 = 2 * s15 * p.2 := by
  simp [Phi, g1, g2]; ring

theorem Psi_Phi (p : ℝ × ℝ) : Psi (Phi p) = p := by
  have h := s15_pos.ne'
  ext
  · simp only [Psi, Phi_apply0, Phi_apply1]; field_simp; ring
  · simp only [Psi, Phi_apply1]; field_simp

theorem Phi_Psi (q : Plane) : Phi (Psi q) = q := by
  have h := s15_pos.ne'
  ext i
  fin_cases i
  · show Phi (Psi q) 0 = q 0
    rw [Phi_apply0]; simp only [Psi]; field_simp; ring
  · show Phi (Psi q) 1 = q 1
    rw [Phi_apply1]; simp only [Psi]; field_simp

theorem Phi_cont : Continuous Phi := by
  unfold Phi; fun_prop

theorem Psi_cont : Continuous Psi := by
  unfold Psi
  have h0 : Continuous fun q : Plane => q 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun q : Plane => q 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  fun_prop

/-- The skew coordinate system as a homeomorphism. -/
noncomputable def PhiH : (ℝ × ℝ) ≃ₜ Plane where
  toFun := Phi
  invFun := Psi
  left_inv := Psi_Phi
  right_inv := Phi_Psi
  continuous_toFun := Phi_cont
  continuous_invFun := Psi_cont

theorem interior_image (S : Set (ℝ × ℝ)) : interior (Phi '' S) = Phi '' interior S :=
  (PhiH.image_interior S).symm

theorem disjoint_image {A B : Set (ℝ × ℝ)} (h : Disjoint (interior A) (interior B)) :
    Disjoint (interior (Phi '' A)) (interior (Phi '' B)) := by
  rw [interior_image, interior_image]
  exact (Set.disjoint_image_iff PhiH.injective).mpr h

theorem Phi_add (p q : ℝ × ℝ) : Phi (p + q) = Phi p + Phi q := by
  unfold Phi; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel


def Sh (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | p - v ∈ S}

theorem image_shift (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    (fun x : Plane => x + Phi v) '' (Phi '' S) = Phi '' Sh v S := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p + v, ?_, by rw [Phi_add]⟩
    show p + v - v ∈ S; simpa using hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Phi (p - v), ⟨p - v, hp, rfl⟩, ?_⟩
    show Phi (p - v) + Phi v = Phi p
    rw [← Phi_add]; simp


noncomputable def shiftR {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ}
    (R : RTiling (Phi '' S) M N) (v : ℝ × ℝ) : RTiling (Phi '' Sh v S) M N :=
  RTiling.cast (image_shift v S) (Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight (Phi v)))

end Erdos634.Draft.WFrame
