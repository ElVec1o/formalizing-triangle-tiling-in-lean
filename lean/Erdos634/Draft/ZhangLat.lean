import Erdos634.Draft.ZhangSporadic

/-!
# Lattice-coordinate toolkit for Zhang's Section 4 constructions (arXiv 2512.22696v4)

Points are written `u e₁ + v e₂` (`e₁ = (1,0)`, `e₂ = (1/2, √3/2)`), the frame of `ZhangPara`
(`uu 0 0`, `vv 0 0`).  `LT` is the triangle with lattice vertices `(u_i, v_i)` (counterclockwise in
the lattice orientation), `ld` the lattice determinant, `Dis_LT_tile1/2` a scaled unit tile in
lattice coordinates (`|s e₁ + t e₂|² = s² + s t + t²`), `Dis.glue_lat` / `Dis.glue_quad_lat` gluing
along one line / a wedge.  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
UNAUDITED.
-/

namespace Erdos634.ZhangLat

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4 Erdos634.ZhangSporadic

/-- lattice determinant -/
def ld (u0 v0 u1 v1 u2 v2 : ℝ) : ℝ := (u1 - u0) * (v2 - v0) - (u2 - u0) * (v1 - v0)

/-- Triangle with lattice vertices. -/
noncomputable def LT (u0 v0 u1 v1 u2 v2 : ℝ) : Set Plane :=
  TriSet (shx 0 u0 v0) (shy 0 v0) (shx 0 u1 v1) (shy 0 v1) (shx 0 u2 v2) (shy 0 v2)

theorem det3_lat (u0 v0 u1 v1 u2 v2 : ℝ) :
    det3 (shx 0 u0 v0) (shy 0 v0) (shx 0 u1 v1) (shy 0 v1) (shx 0 u2 v2) (shy 0 v2)
      = zs / 2 * ld u0 v0 u1 v1 u2 v2 := by
  simp only [det3, shx, shy, ld]; ring

theorem det3_lat_p1 (q : Plane) (u1 v1 u2 v2 : ℝ) :
    det3 (q 0) (q 1) (shx 0 u1 v1) (shy 0 v1) (shx 0 u2 v2) (shy 0 v2)
      = zs / 2 * ld (uu 0 0 q) (vv 0 0 q) u1 v1 u2 v2 := by
  have h0 := q0_eq 0 0 q
  have h1 := q1_eq 0 0 q
  simp only [det3, shx, shy, ld]
  rw [h0, h1]; ring

theorem det3_lat_p2 (q : Plane) (u0 v0 u2 v2 : ℝ) :
    det3 (shx 0 u0 v0) (shy 0 v0) (q 0) (q 1) (shx 0 u2 v2) (shy 0 v2)
      = zs / 2 * ld u0 v0 (uu 0 0 q) (vv 0 0 q) u2 v2 := by
  have h0 := q0_eq 0 0 q
  have h1 := q1_eq 0 0 q
  simp only [det3, shx, shy, ld]
  rw [h0, h1]; ring

theorem det3_lat_p3 (q : Plane) (u0 v0 u1 v1 : ℝ) :
    det3 (shx 0 u0 v0) (shy 0 v0) (shx 0 u1 v1) (shy 0 v1) (q 0) (q 1)
      = zs / 2 * ld u0 v0 u1 v1 (uu 0 0 q) (vv 0 0 q) := by
  have h0 := q0_eq 0 0 q
  have h1 := q1_eq 0 0 q
  simp only [det3, shx, shy, ld]
  rw [h0, h1]; ring

theorem mem_LT (u0 v0 u1 v1 u2 v2 : ℝ) (q : Plane) :
    q ∈ LT u0 v0 u1 v1 u2 v2 ↔
      (0 ≤ ld (uu 0 0 q) (vv 0 0 q) u1 v1 u2 v2 ∧ 0 ≤ ld u0 v0 (uu 0 0 q) (vv 0 0 q) u2 v2 ∧
        0 ≤ ld u0 v0 u1 v1 (uu 0 0 q) (vv 0 0 q)) := by
  have hp : 0 < zs / 2 := by have := zs_pos; positivity
  unfold LT TriSet
  simp only [Set.mem_setOf_eq]
  rw [det3_lat_p1, det3_lat_p2, det3_lat_p3, mul_nonneg_iff_of_pos_left hp,
    mul_nonneg_iff_of_pos_left hp, mul_nonneg_iff_of_pos_left hp]

/-! ### Scaled unit tiles in lattice coordinates -/

section tiles
variable {a b : ℝ}

theorem Dis_LT_tile1 (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) (u0 v0 s1 t1 s2 t2 : ℝ)
    (hU : 0 < ld 0 0 s1 t1 s2 t2) (h1 : s1 ^ 2 + s1 * t1 + t1 ^ 2 = a ^ 2)
    (h2 : s2 ^ 2 + s2 * t2 + t2 ^ 2 = b ^ 2)
    (h12 : (s2 - s1) ^ 2 + (s2 - s1) * (t2 - t1) + (t2 - t1) ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (U1 V1 U2 V2 : ℝ) (hU1 : U1 = u0 + k * s1) (hV1 : V1 = v0 + k * t1)
    (hU2 : U2 = u0 + k * s2) (hV2 : V2 = v0 + k * t2) :
    Dis (Rmodel ha hb) (LT u0 v0 U1 V1 U2 V2) (k * k) := by
  have hz := zs_sq
  have hD : 0 < det3 (shx 0 u0 v0) (shy 0 v0) (shx 0 (u0 + s1) (v0 + t1)) (shy 0 (v0 + t1))
      (shx 0 (u0 + s2) (v0 + t2)) (shy 0 (v0 + t2)) := by
    rw [det3_lat]
    have : ld u0 v0 (u0 + s1) (v0 + t1) (u0 + s2) (v0 + t2) = ld 0 0 s1 t1 s2 t2 := by
      simp only [ld]; ring
    rw [this]
    have := zs_pos
    positivity
  have hUR := unit_cong1 ha hb (shx 0 u0 v0) (shy 0 v0) (shx 0 (u0 + s1) (v0 + t1))
    (shy 0 (v0 + t1)) (shx 0 (u0 + s2) (v0 + t2)) (shy 0 (v0 + t2)) hD
    (by simp only [shx, shy]; linear_combination h1 + (t1 ^ 2 / 4) * hz)
    (by simp only [shx, shy]; linear_combination h2 + (t2 ^ 2 / 4) * hz)
    (by simp only [shx, shy]; linear_combination h12 + ((t2 - t1) ^ 2 / 4) * hz)
  have := Dis_scaled _ _ _ _ _ _ hD hUR k hk (shx 0 U1 V1) (shy 0 V1) (shx 0 U2 V2) (shy 0 V2)
    (by simp only [shx]; rw [hU1, hV1]; ring) (by simp only [shy]; rw [hV1]; ring)
    (by simp only [shx]; rw [hU2, hV2]; ring) (by simp only [shy]; rw [hV2]; ring)
  exact this

theorem Dis_LT_tile2 (ha : 0 < a) (hb : 0 < b) (k : ℕ) (hk : 0 < k) (u0 v0 s1 t1 s2 t2 : ℝ)
    (hU : 0 < ld 0 0 s1 t1 s2 t2) (h1 : s1 ^ 2 + s1 * t1 + t1 ^ 2 = b ^ 2)
    (h2 : s2 ^ 2 + s2 * t2 + t2 ^ 2 = a ^ 2)
    (h12 : (s2 - s1) ^ 2 + (s2 - s1) * (t2 - t1) + (t2 - t1) ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (U1 V1 U2 V2 : ℝ) (hU1 : U1 = u0 + k * s1) (hV1 : V1 = v0 + k * t1)
    (hU2 : U2 = u0 + k * s2) (hV2 : V2 = v0 + k * t2) :
    Dis (Rmodel ha hb) (LT u0 v0 U1 V1 U2 V2) (k * k) := by
  have hz := zs_sq
  have hD : 0 < det3 (shx 0 u0 v0) (shy 0 v0) (shx 0 (u0 + s1) (v0 + t1)) (shy 0 (v0 + t1))
      (shx 0 (u0 + s2) (v0 + t2)) (shy 0 (v0 + t2)) := by
    rw [det3_lat]
    have : ld u0 v0 (u0 + s1) (v0 + t1) (u0 + s2) (v0 + t2) = ld 0 0 s1 t1 s2 t2 := by
      simp only [ld]; ring
    rw [this]
    have := zs_pos
    positivity
  have hUR := unit_cong2 ha hb (shx 0 u0 v0) (shy 0 v0) (shx 0 (u0 + s1) (v0 + t1))
    (shy 0 (v0 + t1)) (shx 0 (u0 + s2) (v0 + t2)) (shy 0 (v0 + t2)) hD
    (by simp only [shx, shy]; linear_combination h1 + (t1 ^ 2 / 4) * hz)
    (by simp only [shx, shy]; linear_combination h2 + (t2 ^ 2 / 4) * hz)
    (by simp only [shx, shy]; linear_combination h12 + ((t2 - t1) ^ 2 / 4) * hz)
  have := Dis_scaled _ _ _ _ _ _ hD hUR k hk (shx 0 U1 V1) (shy 0 V1) (shx 0 U2 V2) (shy 0 V2)
    (by simp only [shx]; rw [hU1, hV1]; ring) (by simp only [shy]; rw [hV1]; ring)
    (by simp only [shx]; rw [hU2, hV2]; ring) (by simp only [shy]; rw [hV2]; ring)
  exact this

end tiles

/-! ### Gluing along lattice lines -/

/-- affine functional `(√3/2)(α u + β v − γ)` for `(α,β) ≠ 0`. -/
noncomputable def lf (α β γ : ℝ) : Plane →ᵃ[ℝ] ℝ :=
  lineFun (shx 0 (γ * α / (α ^ 2 + β ^ 2)) (γ * β / (α ^ 2 + β ^ 2)))
    (shy 0 (γ * β / (α ^ 2 + β ^ 2)))
    (shx 0 (γ * α / (α ^ 2 + β ^ 2)) (γ * β / (α ^ 2 + β ^ 2)) + (β - α / 2))
    (shy 0 (γ * β / (α ^ 2 + β ^ 2)) - α * zs / 2)

theorem lf_apply (α β γ : ℝ) (hN : α ^ 2 + β ^ 2 ≠ 0) (q : Plane) :
    lf α β γ q = zs / 2 * (α * uu 0 0 q + β * vv 0 0 q - γ) := by
  have h0 := q0_eq 0 0 q
  have h1 := q1_eq 0 0 q
  unfold lf
  simp only [lineFun_apply, shx, shy]
  rw [h0, h1]
  field_simp
  ring

theorem lf_linear_ne (α β γ : ℝ) (hN : α ^ 2 + β ^ 2 ≠ 0) : (lf α β γ).linear ≠ 0 := by
  apply lineFun_linear_ne_zero
  by_cases hα : α = 0
  · left
    intro h
    simp only [shx] at h
    have hβ : β ≠ 0 := by intro hb; apply hN; rw [hα, hb]; ring
    have : β - α / 2 = 0 := by linarith
    rw [hα] at this; exact hβ (by linarith)
  · right
    intro h
    simp only [shy] at h
    have := zs_pos
    have : α * zs / 2 = 0 := by linarith
    have h2 : α * zs = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hα h3
    · linarith

theorem lf_nonpos {S : Set Plane} (α β γ : ℝ) (hN : α ^ 2 + β ^ 2 ≠ 0)
    (h : ∀ q ∈ S, α * uu 0 0 q + β * vv 0 0 q ≤ γ) : ∀ q ∈ S, lf α β γ q ≤ 0 := by
  intro q hq
  rw [lf_apply α β γ hN]
  have := h q hq
  have hp : 0 < zs / 2 := by have := zs_pos; positivity
  nlinarith

theorem lf_nonneg {S : Set Plane} (α β γ : ℝ) (hN : α ^ 2 + β ^ 2 ≠ 0)
    (h : ∀ q ∈ S, γ ≤ α * uu 0 0 q + β * vv 0 0 q) : ∀ q ∈ S, 0 ≤ lf α β γ q := by
  intro q hq
  rw [lf_apply α β γ hN]
  have := h q hq
  have hp : 0 < zs / 2 := by have := zs_pos; positivity
  nlinarith

theorem Dis.glue_lat {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1)
    (h2 : Dis R S2 n2) (α β γ : ℝ) (hN : α ^ 2 + β ^ 2 ≠ 0)
    (hS1 : ∀ q ∈ S1, α * uu 0 0 q + β * vv 0 0 q ≤ γ)
    (hS2 : ∀ q ∈ S2, γ ≤ α * uu 0 0 q + β * vv 0 0 q) : Dis R (S1 ∪ S2) (n1 + n2) := by
  obtain ⟨C1, r1, m1⟩ := h1
  obtain ⟨C2, r2, m2⟩ := h2
  refine ⟨glueByLine C1 C2 (m1.trans m2.symm) (lf α β γ) (lf_linear_ne α β γ hN) ?_ ?_, ?_, ?_⟩
  · exact lf_nonpos α β γ hN (fun q hq => hS1 q (by rwa [← r1]))
  · exact lf_nonneg α β γ hN (fun q hq => hS2 q (by rwa [← r2]))
  · simp [r1, r2]
  · simp [m1]

/-- Wedge gluing: `S1` lies in `{α₁u+β₁v ≤ γ₁} ∩ {α₂u+β₂v ≤ γ₂}`, every point of `S2` lies in one of
the opposite closed half-planes. -/
theorem Dis.glue_quad_lat {R : Tri} {S1 S2 : Set Plane} {n1 n2 : ℕ} (h1 : Dis R S1 n1)
    (h2 : Dis R S2 n2) (α β γ α' β' γ' : ℝ) (hN : α ^ 2 + β ^ 2 ≠ 0) (hN' : α' ^ 2 + β' ^ 2 ≠ 0)
    (hS1 : ∀ q ∈ S1, α * uu 0 0 q + β * vv 0 0 q ≤ γ)
    (hS1' : ∀ q ∈ S1, α' * uu 0 0 q + β' * vv 0 0 q ≤ γ')
    (hS2 : ∀ q ∈ S2, γ ≤ α * uu 0 0 q + β * vv 0 0 q ∨ γ' ≤ α' * uu 0 0 q + β' * vv 0 0 q) :
    Dis R (S1 ∪ S2) (n1 + n2) := by
  refine Dis.glue_disj h1 h2 ?_
  refine (disjoint_quadrant (S := S2) (T := S1) (lf α β γ) (lf α' β' γ') (lf_linear_ne α β γ hN)
    (lf_linear_ne α' β' γ' hN') (lf_nonpos α β γ hN hS1) (lf_nonpos α' β' γ' hN' hS1') ?_).symm
  intro q hq
  have hp : 0 < zs / 2 := by have := zs_pos; positivity
  rcases hS2 q hq with h | h
  · left; rw [lf_apply α β γ hN]; nlinarith
  · right; rw [lf_apply α' β' γ' hN']; nlinarith

end Erdos634.ZhangLat
