-- Draft/CollarParam.lean — skew lattice coordinates for the (1,2) collar: `Φ(s,t) = s·e₁ + t·e₂`,
-- `e₁ = (88,0)`, `e₂ = (44, 12√15)`.  `Δ_m = Φ{s,t ≥ 0, s+t ≤ m}`, the unit parallelogram is
-- `Φ[0,1]²`, and the collar is a union of coordinate rectangles/triangles.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RegionTiling
import Erdos634.CertCoord

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.CollarParam

noncomputable def s15 : ℝ := Real.sqrt 15
theorem s15_pos : 0 < s15 := Real.sqrt_pos.mpr (by norm_num)
theorem s15_sq : s15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)

noncomputable def e1 : Plane := mkPt 88 0
noncomputable def e2 : Plane := mkPt 44 (12 * s15)

/-- Skew coordinates → plane. -/
noncomputable def Phi (p : ℝ × ℝ) : Plane := p.1 • e1 + p.2 • e2

/-- Plane → skew coordinates. -/
noncomputable def Psi (q : Plane) : ℝ × ℝ :=
  ((q 0 - q 1 * (44 / (12 * s15))) / 88, q 1 / (12 * s15))

theorem Phi_apply0 (p : ℝ × ℝ) : Phi p 0 = 88 * p.1 + 44 * p.2 := by
  simp [Phi, e1, e2]; ring

theorem Phi_apply1 (p : ℝ × ℝ) : Phi p 1 = 12 * s15 * p.2 := by
  simp [Phi, e1, e2]; ring

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

/-- Separation by a vertical line `s = c` (half-planes in skew coordinates). -/
theorem interior_disj_fst {A B : Set (ℝ × ℝ)} (c : ℝ) (hA : ∀ p ∈ A, p.1 ≤ c)
    (hB : ∀ p ∈ B, c ≤ p.1) : Disjoint (interior A) (interior B) := by
  rw [Set.disjoint_left]
  intro p hpA hpB
  obtain ⟨ε, hε, hballA⟩ := Metric.isOpen_iff.mp isOpen_interior p hpA
  obtain ⟨δ, hδ, hballB⟩ := Metric.isOpen_iff.mp isOpen_interior p hpB
  set r := min ε δ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hmem : ∀ x : ℝ × ℝ, dist x p < min ε δ → x ∈ interior A ∧ x ∈ interior B := by
    intro x hx
    exact ⟨hballA (lt_of_lt_of_le hx (min_le_left _ _)), hballB (lt_of_lt_of_le hx (min_le_right _ _))⟩
  have hx1 := (hmem (p.1 + r, p.2) (by
    rw [Prod.dist_eq]; simp [Real.dist_eq, abs_of_pos hrpos]
    refine ⟨⟨?_, hε⟩, ?_, hδ⟩ <;> linarith [min_le_left ε δ, min_le_right ε δ, lt_min hε hδ])).1
  have hx2 := (hmem (p.1 - r, p.2) (by
    rw [Prod.dist_eq]; simp [Real.dist_eq, abs_of_pos hrpos]
    refine ⟨⟨?_, hε⟩, ?_, hδ⟩ <;> linarith [min_le_left ε δ, min_le_right ε δ, lt_min hε hδ])).2
  have a1 := hA _ (interior_subset hx1)
  have b1 := hB _ (interior_subset hx2)
  simp only at a1 b1
  linarith

theorem interior_disj_snd {A B : Set (ℝ × ℝ)} (c : ℝ) (hA : ∀ p ∈ A, p.2 ≤ c)
    (hB : ∀ p ∈ B, c ≤ p.2) : Disjoint (interior A) (interior B) := by
  have sw : ∀ S : Set (ℝ × ℝ), interior (Prod.swap '' S) = Prod.swap '' interior S := fun S =>
    (Homeomorph.prodComm ℝ ℝ).image_interior S |>.symm
  have := interior_disj_fst (A := Prod.swap '' A) (B := Prod.swap '' B) c
    (by rintro _ ⟨p, hp, rfl⟩; exact hA p hp) (by rintro _ ⟨p, hp, rfl⟩; exact hB p hp)
  rw [sw, sw] at this
  exact (Set.disjoint_image_iff Prod.swap_injective).mp this

open Erdos634.Draft.RegionTiling

def RTiling.cast {S S' : Set Plane} {M : Tri} {N : ℕ} (h : S = S') (R : RTiling S M N) :
    RTiling S' M N := h ▸ R

theorem Phi_add (p q : ℝ × ℝ) : Phi (p + q) = Phi p + Phi q := by
  unfold Phi; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel

/-- `{p | p - v ∈ S}`: `S` shifted by `v` in skew coordinates. -/
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

/-- Translate a region tiling by `v` in skew coordinates. -/
noncomputable def shiftR {S : Set (ℝ × ℝ)} {M : Tri} {N : ℕ}
    (R : RTiling (Phi '' S) M N) (v : ℝ × ℝ) : RTiling (Phi '' Sh v S) M N :=
  RTiling.cast (image_shift v S) (Erdos634.Draft.RegionTiling.map R (IsometryEquiv.addRight (Phi v)))

def Tset (m : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ m}
def Rect (a b c d : ℝ) : Set (ℝ × ℝ) := {p | a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d}

theorem Tset_step (m : ℝ) (hm : 0 ≤ m) :
    (Sh (0, 2) (Tset m) ∪ Rect 0 m 0 2) ∪ Sh (m, 0) (Tset 2) = Tset (m + 2) := by
  ext p
  simp only [Sh, Tset, Rect, Set.mem_union, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩) | ⟨h1, h2, h3⟩)
    · refine ⟨h1, by linarith, by linarith⟩
    · refine ⟨h1, by linarith, by linarith⟩
    · refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases ht : 2 ≤ p.2
    · left; left; exact ⟨h1, by linarith, by linarith⟩
    · by_cases hs : p.1 ≤ m
      · left; right; exact ⟨h1, hs, h2, by linarith⟩
      · right; exact ⟨by linarith, h2, by linarith⟩

/-- **The collar step in region form.** -/
noncomputable def collar_step {M : Tri} {N : ℕ} (m : ℕ)
    (RA : RTiling (Phi '' Tset m) M N)
    (RB : RTiling (Phi '' Rect 0 m 0 2) M (44 * m))
    (RC : RTiling (Phi '' Tset 2) M 44) :
    RTiling (Phi '' Tset ((m : ℝ) + 2)) M (N + 44 * m + 44) := by
  have hApex := shiftR RA (0, 2)
  have hCorner := shiftR RC ((m : ℝ), 0)
  have hd1 : Disjoint (interior (Phi '' Sh (0, 2) (Tset m))) (interior (Phi '' Rect 0 m 0 2)) := by
    refine disjoint_image (interior_disj_snd 2 ?_ ?_).symm
    · rintro p ⟨h1, h2, h3, h4⟩; exact h4
    · rintro p ⟨h1, h2, h3⟩; simp only [Prod.snd_sub] at h2; linarith
  have hd2 : Disjoint (interior (Phi '' Sh (0, 2) (Tset m) ∪ Phi '' Rect 0 m 0 2))
      (interior (Phi '' Sh ((m : ℝ), 0) (Tset 2))) := by
    rw [← Set.image_union]
    refine disjoint_image (interior_disj_fst (m : ℝ) ?_ ?_)
    · rintro p (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
      · simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 ⊢; linarith
      · exact h2
    · rintro p ⟨h1, h2, h3⟩
      simp only [Prod.fst_sub, Prod.snd_sub] at h1 ⊢; linarith
  have U := Erdos634.Draft.RegionTiling.union (Erdos634.Draft.RegionTiling.union hApex RB hd1) hCorner hd2
  refine RTiling.cast ?_ U
  rw [← Set.image_union, ← Set.image_union, Tset_step (m : ℝ) (Nat.cast_nonneg m)]

def RTiling.castN {S : Set Plane} {M : Tri} {N N' : ℕ} (h : N = N') (R : RTiling S M N) :
    RTiling S M N' := h ▸ R

theorem Sh_Rect (v : ℝ × ℝ) (a b c d : ℝ) :
    Sh v (Rect a b c d) = Rect (a + v.1) (b + v.1) (c + v.2) (d + v.2) := by
  ext p
  simp only [Sh, Rect, Set.mem_setOf_eq, Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A column of two unit squares from a unit-square tiling. -/
noncomputable def column {M : Tri} (U : RTiling (Phi '' Rect 0 1 0 1) M 22) (j : ℝ) :
    RTiling (Phi '' Rect j (j + 1) 0 2) M 44 := by
  have h0 := shiftR U (j, 0)
  have h1 := shiftR U (j, 1)
  rw [Sh_Rect] at h0 h1
  have hd : Disjoint (interior (Phi '' Rect (0 + j) (1 + j) (0 + 0) (1 + 0)))
      (interior (Phi '' Rect (0 + j) (1 + j) (0 + 1) (1 + 1))) := by
    refine disjoint_image (interior_disj_snd 1 ?_ ?_)
    · rintro p ⟨a, b, c, d⟩; simpa using d
    · rintro p ⟨a, b, c, d⟩; simpa using c
  have := Erdos634.Draft.RegionTiling.union h0 h1 hd
  refine RTiling.castN (by norm_num) (RTiling.cast ?_ this)
  rw [← Set.image_union]
  congr 1
  ext p
  simp only [Rect, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨a, b, c, d⟩ | ⟨a, b, c, d⟩)
    · refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c, d⟩
    by_cases h : p.2 ≤ 1
    · left; refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · right; refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The band of `k+1` columns. -/
noncomputable def bandS {M : Tri} (U : RTiling (Phi '' Rect 0 1 0 1) M 22) :
    (k : ℕ) → RTiling (Phi '' Rect 0 ((k : ℝ) + 1) 0 2) M (44 * (k + 1))
  | 0 => by
      have := column U 0
      rw [zero_add] at this
      exact RTiling.cast (by simp) this
  | k + 1 => by
      have hc := column U ((k : ℝ) + 1)
      have hd : Disjoint (interior (Phi '' Rect 0 ((k : ℝ) + 1) 0 2))
          (interior (Phi '' Rect ((k : ℝ) + 1) ((k : ℝ) + 1 + 1) 0 2)) := by
        refine disjoint_image (interior_disj_fst ((k : ℝ) + 1) ?_ ?_)
        · rintro p ⟨a, b, c, d⟩; exact b
        · rintro p ⟨a, b, c, d⟩; exact a
      have := Erdos634.Draft.RegionTiling.union (bandS U k) hc hd
      refine RTiling.castN (by ring) (RTiling.cast ?_ this)
      rw [← Set.image_union]
      congr 1
      push_cast
      ext p
      simp only [Rect, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (⟨a, b, c, d⟩ | ⟨a, b, c, d⟩)
        · refine ⟨a, by linarith, c, d⟩
        · refine ⟨by linarith, b, c, d⟩
      · rintro ⟨a, b, c, d⟩
        by_cases h : p.1 ≤ (k : ℝ) + 1
        · left; exact ⟨a, h, c, d⟩
        · right; exact ⟨by linarith, by linarith, c, d⟩

/-- **The collar induction.**  From a unit-square tiling `U` (22 tiles), a tiling of `Δ₂` (44 tiles)
and of `Δ₃` (99 tiles), every `Δ_m`, `m ≥ 2`, is tiled by `11 m²` tiles of the same model. -/
theorem realize_all {M : Tri} (U : RTiling (Phi '' Rect 0 1 0 1) M 22)
    (R2 : RTiling (Phi '' Tset 2) M 44) (R3 : RTiling (Phi '' Tset 3) M 99) :
    ∀ m : ℕ, 2 ≤ m → Nonempty (RTiling (Phi '' Tset (m : ℝ)) M (11 * (m * m))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h2 : m = 2
    · subst h2; exact ⟨RTiling.castN (by norm_num) (RTiling.cast (by norm_num) R2)⟩
    by_cases h3 : m = 3
    · subst h3; exact ⟨RTiling.castN (by norm_num) (RTiling.cast (by norm_num) R3)⟩
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    have hj : 2 ≤ j := by omega
    obtain ⟨RA⟩ := ih j (by omega) hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have RB := bandS U k
    have RB' : RTiling (Phi '' Rect 0 ((k + 1 : ℕ) : ℝ) 0 2) M (44 * (k + 1)) := by
      refine RTiling.cast ?_ RB; push_cast; rfl
    have := collar_step (k + 1) RA RB' R2
    exact ⟨RTiling.castN (by ring) (RTiling.cast (by push_cast; ring_nf) this)⟩

end Erdos634.Draft.CollarParam

#print axioms Erdos634.Draft.CollarParam.realize_all
