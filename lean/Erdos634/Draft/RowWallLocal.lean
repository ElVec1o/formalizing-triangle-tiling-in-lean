-- Draft/RowWallLocal.lean — the LOCAL steps of RW(j) ((private working notes, not included) S1,
-- proof_H_empty.md §5.5), for real dissections in the apex frame, on the `Λ₃` lattice of
-- Draft/RowWallReal.lean.  Imported into All.lean (Erdos634/All.lean:421).
--
-- Build (scratch oleans; never .lake): RowWallReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/RowWallLocal.lean'
--
-- The steps, each named by the paper's step and by where `m = 1` enters:
--   `slot_int`  (A), interior slot `Λ(i+1,t+1)`: the residual `α` is the up cell or the swap.
--               (No `m = 1` input: angle counting, `C2` = α indecomposable via `AngleData.hirr`.)
--   `slot_leg`  (A), `i = 0`: the leg slot is the up cell.  m = 1: the leg is `b`-free
--               (`lem:sidenob`, `LFrame.hlegnob`).
--   `junc_kill` Lemma A on `L_j`: no right-side junction at `Λ(j,T)`, `T ≤ f − j`, once a `b` sits on
--               the right side.  m = 1: `Inflation.c_side_no_b` (`T < f`; at N = 44, 2c = a + 2b).
--   `cross_kill` (A), `i = j − 1`: the swap's `c`-edge crosses `L_j` where `L_j` is straddled.
--   `row_step`  (B): the next row is `a^j` and its down cells are half-turns.  m = 1:
--               `Inflation.a_side_no_b` + `a_side_rigid` (`j < f`; at N = 44, 2a = c).
--   `start_of_up`, `seed_of_Xs`, `base_nstr`: the bookkeeping of hypothesis `C(j,m)`(ii).
import Erdos634.Draft.RowWallReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §0 Constants and small helpers -/

include F in
theorem consts : (0 : ℝ) < (e : ℝ) * f ∧ (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
    (0 : ℝ) < (f : ℝ) ^ 2 ∧ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 ∧
    (e : ℝ) * f < (f : ℝ) ^ 2 := by
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem Lam_sub_eq {x y x' y' p q : ℝ} (h1 : x - x' = p) (h2 : y - y' = q) :
    Lam F x y - Lam F x' y' = vec F p q := by
  rw [Lam_sub, h1, h2]

theorem Lam_add_eq {x y p q x' y' : ℝ} (h1 : x + p = x') (h2 : y + q = y') :
    Lam F x y + vec F p q = Lam F x' y' := by
  rw [Lam_add, h1, h2]

theorem vec_sub (p q r s : ℝ) : vec F p q - vec F r s = vec F (p - r) (q - s) := by
  simp only [vec]; module

theorem norm_vec_p0 {p : ℝ} (hp : 0 ≤ p) : ‖vec F p 0‖ = p * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  simp [vec, norm_smul, norm_w, Real.norm_of_nonneg hp]

theorem norm_vec_0q {q : ℝ} (hq : 0 ≤ q) : ‖vec F 0 q‖ = q * (f : ℝ) ^ 2 := by
  simp [vec, norm_smul, norm_v, Real.norm_of_nonneg hq]

theorem norm_vec_m10 : ‖vec F (-1) 0‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [show vec F (-1) 0 = - vec F 1 0 by rw [vec_neg]; norm_num, norm_neg, norm_vec_10]

theorem norm_vec_1m1 : ‖vec F 1 (-1)‖ = (e : ℝ) * f := by
  rw [show vec F 1 (-1) = - vec F (-1) 1 by rw [vec_neg]; norm_num, norm_neg, norm_vec_m11]

theorem dist_add_vec (X : Plane) (p q r s : ℝ) :
    dist (X + vec F p q) (X + vec F r s) = ‖vec F (p - r) (q - s)‖ := by
  rw [dist_add_left, dist_eq_norm, vec_sub]

theorem K_ne (FC : ApexPlacement.FrameCoords F) : (f : ℝ) ^ 2 * cross (w F) F.uL ≠ 0 :=
  mul_ne_zero (cf_pos F).ne' (kappa_ne F FC)

/-- Two distinct vertices of a triangle are the ends of one of its edges. -/
theorem edge_idx {T : Tri} {P Q : Plane} (hP : P ∈ Set.range T.pts) (hQ : Q ∈ Set.range T.pts)
    (hPQ : P ≠ Q) :
    ∃ m : Fin 3, (T.pts m = P ∧ T.pts (m + 1) = Q) ∨ (T.pts m = Q ∧ T.pts (m + 1) = P) := by
  obtain ⟨k0, rfl⟩ := hP
  obtain ⟨k1, rfl⟩ := hQ
  rcases fin3_cases3 k0 k1 with h | h | h
  · exact absurd (by rw [h]) hPQ
  · exact ⟨k0, Or.inl ⟨rfl, by rw [h]⟩⟩
  · refine ⟨k1, Or.inr ⟨rfl, ?_⟩⟩
    rw [h]; congr 1; fin_cases k0 <;> decide

/-- A pair set equality with distinct members, as two orders. -/
theorem pair_cases {p q P Q : Plane} (h : ({p, q} : Set Plane) = {P, Q}) (hpq : p ≠ q) :
    (p = P ∧ q = Q) ∨ (p = Q ∧ q = P) := by
  have hp : p ∈ ({P, Q} : Set Plane) := h ▸ (by simp)
  have hq : q ∈ ({P, Q} : Set Plane) := h ▸ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hpq

theorem mem3_1 {a b c : Plane} : a ∈ ({a, b, c} : Set Plane) := Set.mem_insert _ _
theorem mem3_2 {a b c : Plane} : b ∈ ({a, b, c} : Set Plane) :=
  Set.mem_insert_of_mem _ (Set.mem_insert _ _)
theorem mem3_3 {a b c : Plane} : c ∈ ({a, b, c} : Set Plane) :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

/-- `z ≠ iT` from flank directions, lattice form (the differences given as numerals). -/
theorem ne_of_flank_lam (FC : ApexPlacement.FrameCoords F) {z iT : Fin N} {mz : Fin 3}
    {x y x1 y1 x2 y2 p q d1 e1 d2 e2 : ℝ} {U W : Plane} {S : ℝ}
    (hmz : (D.tile z).pts mz = Lam F x y) (hUW : IsFlankPair (D.tile z) mz (Lam F x y) U W)
    (hS : 0 < S) (hU0 : vec F p q = S • U)
    (hr : Set.range (D.tile iT).pts = {Lam F x y, Lam F x1 y1, Lam F x2 y2})
    (hd1 : x1 - x = d1) (he1 : y1 - y = e1) (hd2 : x2 - x = d2) (he2 : y2 - y = e2)
    (h1 : ∀ S' : ℝ, 0 < S' → p = S' * d1 → q = S' * e1 → False)
    (h2 : ∀ S' : ℝ, 0 < S' → p = S' * d2 → q = S' * e2 → False) : z ≠ iT := by
  refine ne_of_flank hmz hUW hS hU0 hr ?_ ?_
  · rw [Lam_sub, hd1, he1]; exact vec_ne_smul F FC h1
  · rw [Lam_sub, hd2, he2]; exact vec_ne_smul F FC h2

/-- A lattice point not among three others. -/
theorem not_mem3 (FC : ApexPlacement.FrameCoords F) {x y x1 y1 x2 y2 x3 y3 : ℝ}
    (h1 : x ≠ x1 ∨ y ≠ y1) (h2 : x ≠ x2 ∨ y ≠ y2) (h3 : x ≠ x3 ∨ y ≠ y3) :
    Lam F x y ∉ ({Lam F x1 y1, Lam F x2 y2, Lam F x3 y3} : Set Plane) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨Lam_ne F FC h1, Lam_ne F FC h2, Lam_ne F FC h3⟩

theorem vec_coords (FC : ApexPlacement.FrameCoords F) (u : Plane) :
    u = vec F (col F u) (rho F u) := by
  have hk := kappa_ne F FC
  set r := u - vec F (col F u) (rho F u) with hr
  have hc : col F r = 0 := by rw [hr, map_sub, col_vec F FC]; ring
  have hq : rho F r = 0 := by rw [hr, map_sub, rho_vec F FC]; ring
  have hc0 : (f : ℝ) ^ 2 ≠ 0 := (cf_pos F).ne'
  simp only [col, rho, LinearMap.smul_apply, LinearMap.neg_apply, crossL_apply, smul_eq_mul]
    at hc hq
  have e1 : cross F.uL r = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h (one_div_ne_zero hk)
    · linarith
  have e2 : cross (w F) r = 0 := by
    rcases mul_eq_zero.mp hq with h | h
    · exact absurd h (one_div_ne_zero (mul_ne_zero hc0 hk))
    · exact h
  rw [NearBaseVertex.cross_apply] at e1 e2 hk
  have r0 : r 0 = 0 := by
    have : r 0 * ((w F) 0 * F.uL 1 - (w F) 1 * F.uL 0) = 0 := by
      linear_combination -(w F) 0 * e1 + F.uL 0 * e2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hk
  have r1 : r 1 = 0 := by
    have : r 1 * ((w F) 0 * F.uL 1 - (w F) 1 * F.uL 0) = 0 := by
      linear_combination -(w F) 1 * e1 + F.uL 1 * e2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hk
  have : r = 0 := by
    ext i; fin_cases i
    · simpa using r0
    · simpa using r1
  rw [hr] at this
  exact sub_eq_zero.mp this

/-- Two points with the same `col` and `lev` coincide. -/
theorem eq_of_col_lev (FC : ApexPlacement.FrameCoords F) {p q : Plane} (h1 : col F p = col F q)
    (h2 : lev F p = lev F q) : p = q := by
  have h3 : rho F p = rho F q := by
    simp only [lev, LinearMap.add_apply] at h2; linarith
  have := vec_coords F FC (p - q)
  rw [map_sub, map_sub, h1, h3, sub_self, sub_self, vec_zero] at this
  exact sub_eq_zero.mp this

/-! ## §1 The `α`-tile across `w` (the slot dichotomy, `C2`) -/

/-- **The slot dichotomy.**  At `Λ(x,y)`, an `α`-tile with one flank positively along `w` and the
other on the far side of `ℝw` from `w − v` is the up cell `{Λ(x,y), Λ(x+1,y), Λ(x,y+1)}` (`b` on
`w`) or the swap `Xs x y` (`c` on `w`, `b` down the row line) — `corner_dataH` (flanks `{b, c}`,
opposite `a`) and `ident`.  No `m = 1` input. -/
theorem alpha_at (FC : ApexPlacement.FrameCoords F) {z : Fin N} {mz : Fin 3} {x y : ℝ}
    {U W : Plane} {S : ℝ} (hmz : (D.tile z).pts mz = Lam F x y)
    (hUW : IsFlankPair (D.tile z) mz (Lam F x y) U W) (hS : 0 < S) (hU0 : vec F 1 0 = S • U)
    (hside : cross (vec F 1 0) W * cross (vec F 1 0) (vec F 1 (-1)) < 0)
    (hα : (D.tile z).localAngle (Lam F x y) = α) :
    Set.range (D.tile z).pts = {Lam F x y, Lam F (x + 1) y, Lam F x (y + 1)} ∨
      Set.range (D.tile z).pts = Xs F x y := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hK := K_ne F FC
  have hK2 : 0 < ((f : ℝ) ^ 2 * cross (w F) F.uL) * ((f : ℝ) ^ 2 * cross (w F) F.uL) :=
    mul_self_pos.mpr hK
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hα
  have hL0 := norm_vec_10 F
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hU : U = vec F 1 0 := by
      rw [flank_eq hS hU0 h1 hL0 hb0, div_self hb0.ne', one_smul]
    have hs2 : cross (vec F 1 0) (vec F 0 1) * cross (vec F 1 0) (vec F 1 (-1)) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU (by intro h; rw [h, norm_zero] at hL0; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_01]) (by rw [hopp, dist_add_vec, sub_zero, zero_sub, norm_vec_1m1])
    rw [hr, Lam_add_eq F rfl (add_zero y), Lam_add_eq F (add_zero x) rfl]
  · right
    have hU : U = vec F ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0 := by
      rw [flank_eq hS hU0 h1 hL0 hb0, vec_smul, mul_one, mul_zero]
    have hq : (0 : ℝ) ≤ ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
    have hs2 : cross (vec F 1 0) (vec F 0 (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))
        * cross (vec F 1 0) (vec F 1 (-1)) < 0 := by
      rw [cross_vec, cross_vec]
      have : 0 < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
      nlinarith
    have hUne : vec F ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0 ≠ 0 := by
      intro h
      have := norm_vec_p0 F (p := (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (by positivity)
      rw [h, norm_zero] at this
      have : 0 < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
        positivity
      linarith
    have hr := ident hmz hUW hU hUne
      (by have := side_of_across hS hU0 hside hs2; rwa [hU] at this)
      (by rw [h2, norm_vec_0q F hq, div_mul_cancel₀ _ hc0.ne'])
      (by rw [hopp, dist_add_vec, sub_zero, zero_sub, norm_vec_swap])
    rw [hr, Xs, Lam_add_eq F rfl (add_zero y), Lam_add_eq F (add_zero x) rfl]

/-! ## §2 (A) the slots of band `B_m` -/

/-- **(A), interior slot `Λ(i+1, t+1)`** (strip `i+2`, row `i+t+2`).  Around it: `Dn i t` (`α`),
`Up (i+1) t`, `Dn i (t+1)` (`β`, `β`), `Up i (t+1)`, `Dn (i+1) t` (`γ`, `γ`); the figure is
`{2α, 2β, 2γ}` (`interior_card_eqs`), so the tile across `Dn (i+1) t`'s flank `w` is the residual
`α`-tile: the up cell `Up (i+1) (t+1)` or the swap `Xs` (`alpha_at`).  No `m = 1` input. -/
theorem slot_int (L : LFrame F) (i t : ℕ) (hit : i + t + 3 ≤ f)
    (hA : Present D (Dn F i t)) (hB1 : Present D (Up F (i + 1) t))
    (hB2 : Present D (Dn F i (t + 1))) (hG1 : Present D (Up F i (t + 1)))
    (hG2 : Present D (Dn F (i + 1) t)) :
    Present D (Up F (i + 1) (t + 1)) ∨ Present D (Xs F ((i : ℝ) + 1) ((t : ℝ) + 1)) := by
  classical
  have FC := L.FC
  have hitR : (i : ℝ) + t + 3 ≤ f := by exact_mod_cast hit
  have hXint : Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) (by positivity) (by linarith)
  obtain ⟨iA, hrA⟩ := hA
  obtain ⟨iB1, hrB1⟩ := hB1
  obtain ⟨iB2, hrB2⟩ := hB2
  obtain ⟨iG1, hrG1⟩ := hG1
  obtain ⟨iG2, hrG2⟩ := hG2
  have gA : (D.tile iA).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = α := (Dn_angles F hrA).2.2
  have gB1 : (D.tile iB1).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = β := by
    have := (Up_angles F hrB1).2.2; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
  have gB2 : (D.tile iB2).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = β := by
    have := (Dn_angles F hrB2).1; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
  have gG1 : (D.tile iG1).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
    have := (Up_angles F hrG1).2.1; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
  have gG2 : (D.tile iG2).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
    have := (Dn_angles F hrG2).2.1; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
  have rB1 : Set.range (D.tile iB1).pts = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Lam F ((i : ℝ) + 1) t, Lam F ((i : ℝ) + 1 + 1) t} := by
    rw [hrB1]; simp only [Up, Nat.cast_add, Nat.cast_one]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rB2 : Set.range (D.tile iB2).pts = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Lam F i ((t : ℝ) + 1 + 1), Lam F ((i : ℝ) + 1) ((t : ℝ) + 1 + 1)} := by
    rw [hrB2]; simp only [Dn, Nat.cast_add, Nat.cast_one]
  have rG1 : Set.range (D.tile iG1).pts = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Lam F i ((t : ℝ) + 1), Lam F i ((t : ℝ) + 1 + 1)} := by
    rw [hrG1]; simp only [Up, Nat.cast_add, Nat.cast_one]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rG2 : Set.range (D.tile iG2).pts = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Lam F ((i : ℝ) + 1 + 1) ((t : ℝ) + 1), Lam F ((i : ℝ) + 1 + 1) t} := by
    rw [hrG2]; simp only [Dn, Nat.cast_add, Nat.cast_one]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hG12 : iG1 ≠ iG2 := ne_of_range rG1 rG2 (p := Lam F i ((t : ℝ) + 1)) (by simp)
    (not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
      (Or.inl (by intro h; linarith)))
  have hB12 : iB1 ≠ iB2 := ne_of_range rB1 rB2 (p := Lam F ((i : ℝ) + 1) t) (by simp)
    (not_mem3 F FC (Or.inr (by intro h; linarith)) (Or.inl (by intro h; linarith))
      (Or.inr (by intro h; linarith)))
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG2
  rw [Lam_sub_eq F (by ring : ((i : ℝ) + 1 + 1) - ((i : ℝ) + 1) = 1)
      (by ring : ((t : ℝ) + 1) - ((t : ℝ) + 1) = 0),
    Lam_sub_eq F (by ring : ((i : ℝ) + 1 + 1) - ((i : ℝ) + 1) = 1)
      (by ring : (t : ℝ) - ((t : ℝ) + 1) = -1)] at hflG
  obtain ⟨z, hzG, hXz, hcase⟩ := flank_neighbour_dissection D.toDissection hXint hmG hflG
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  have cA := card_one gA
  have cB := card_two hB12 gB1 gB2
  have cG := card_two hG12 gG1 gG2
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m' hmpos
    rcases localAngle_mem_pi_of_mem (D.tile z) hXz hznv with h | h
    · have := card_one h; omega
    · have := card_one h; omega
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · rcases alpha_at F FC hmz hUW hS hU0 hside hz with h | h
    · left; refine ⟨z, ?_⟩; rw [h]; simp only [Up, Nat.cast_add, Nat.cast_one]
    · right; exact ⟨z, h⟩
  · exfalso
    rcases mem_of_card_two hB12 gB1 gB2 (by omega) hz with rfl | rfl
    · exact ne_of_flank_lam F FC hmz hUW hS hU0 rB1 (d1 := 0) (e1 := -1) (d2 := 1) (e2 := -1)
        (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
    · exact ne_of_flank_lam F FC hmz hUW hS hU0 rB2 (d1 := -1) (e1 := 1) (d2 := 0) (e2 := 1)
        (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
  · exfalso
    rcases mem_of_card_two hG12 gG1 gG2 (by omega) hz with rfl | rfl
    · exact ne_of_flank_lam F FC hmz hUW hS hU0 rG1 (d1 := -1) (e1 := 0) (d2 := -1) (e2 := 1)
        (by ring) (by ring) (by ring) (by ring)
        (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) rfl
    · exact hzG rfl

/-- **(A), the leg slot `J_{t+1} = Λ(0, t+1)`** (`prop:selfsim`; generalizes
`MirrorStripR2Real.leg_step`, which is stated for the (M)-branch frame `R2Frame`).  `Up 0 t` (`β`) and
`Dn 0 t` (`γ`) leave one `α` at the leg point (`gamma_boundary_figure_real`); the tile across
`Dn 0 t`'s flank `w` is the up cell `Up 0 (t+1)`, the swap being excluded because it would lay a
`b`-edge on the leg.  **m = 1 enters here**: the leg is `b`-free (`lem:sidenob`, `LFrame.hlegnob`). -/
theorem slot_leg (L : LFrame F) (t : ℕ) (ht : t + 3 ≤ f)
    (hB : Present D (Up F 0 t)) (hG : Present D (Dn F 0 t)) : Present D (Up F 0 (t + 1)) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hK := K_ne F FC
  have htR : (t : ℝ) + 3 ≤ f := by exact_mod_cast ht
  have hAD := F.hAng
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, -, -, -⟩ := ApexPlacement.angle_facts hAD
  have hXf : Lam F 0 ((t : ℝ) + 1) ∈ frontier D.target.carrier :=
    leg_frontier F FC (by positivity) (by linarith)
  have hXv : Lam F 0 ((t : ℝ) + 1) ∉ Set.range D.target.pts :=
    leg_not_vertex F FC (by positivity) (by linarith)
  obtain ⟨iB, hrB⟩ := hB
  obtain ⟨iG, hrG⟩ := hG
  have gB : (D.tile iB).localAngle (Lam F 0 ((t : ℝ) + 1)) = β := by
    have := (Up_angles F hrB).2.2; simp only [Nat.cast_zero] at this; exact this
  have gG : (D.tile iG).localAngle (Lam F 0 ((t : ℝ) + 1)) = γ := by
    have := (Dn_angles F hrG).2.1; simp only [Nat.cast_zero] at this; exact this
  have hvals := fun i => Dissection.congruentDissection_localAngle_mem_boundary D α β γ F.hM.hα'
    F.hM.hβ' F.hM.hγ' hXf hXv i
  obtain ⟨cA, cB, cC, cP⟩ := VertexFigureReal.gamma_boundary_figure_real D.toDissection hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 Real.pi_ne_zero hAD.hγdef hAD.hrel hAD.hirr hXf hXv hvals iG gG
  have hvert : ∀ i, Lam F 0 ((t : ℝ) + 1) ∈ (D.tile i).carrier →
      ∃ m, (D.tile i).pts m = Lam F 0 ((t : ℝ) + 1) := by
    intro i hi
    by_contra hv; push Not at hv
    rcases localAngle_mem_pi_of_mem (D.tile i) hi hv with h | h
    · have := hvals i; rw [h] at this; exact two_pi_not_mem hAD this
    · have := card_one h; omega
  have rG : Set.range (D.tile iG).pts = {Lam F 0 ((t : ℝ) + 1), Lam F 1 ((t : ℝ) + 1),
      Lam F 1 t} := by
    rw [hrG]; simp only [Dn, Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rB : Set.range (D.tile iB).pts = {Lam F 0 ((t : ℝ) + 1), Lam F 0 t, Lam F 1 t} := by
    rw [hrB]; simp only [Up, Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG
  rw [Lam_sub_eq F (by ring : (1 : ℝ) - 0 = 1) (by ring : ((t : ℝ) + 1) - ((t : ℝ) + 1) = 0),
    Lam_sub_eq F (by ring : (1 : ℝ) - 0 = 1) (by ring : (t : ℝ) - ((t : ℝ) + 1) = -1)] at hflG
  have hΔ : cross (vec F 1 0) (vec F 1 (-1)) ≠ 0 := by
    rw [cross_vec]; intro h; apply hK; linarith
  have hN : 0 < N := Fin.pos iG
  have hcovn : ∀ n : ℕ, ∃ (j : Fin N) (ε : ℝ), 0 < ε ∧ Lam F 0 ((t : ℝ) + 1) ∈ (D.tile j).carrier ∧
      Lam F 0 ((t : ℝ) + 1) + ε • (vec F 1 0 - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • vec F 1 (-1))
        ∈ (D.tile j).carrier := by
    intro n
    have hs0 : (0 : ℝ) < 1 / ((n : ℝ) + ((1 : ℕ) : ℝ)) := by positivity
    have hs1 : 1 / ((n : ℝ) + ((1 : ℕ) : ℝ)) ≤ 1 := by
      rw [Nat.cast_one, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hD0 : vec F 1 0 - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • vec F 1 (-1) ≠ 0 := by
      rw [vec_smul, vec_sub]; intro h; rw [← vec_zero F] at h
      have := (vec_inj F FC h).2; linarith
    refine ApexPlacement.cover_tile_dir D.tile _ hN hD0 one_pos (fun τ hτ hτ1 => ?_)
    rw [D.covers, vec_smul, vec_sub, vec_smul, Lam_add]
    apply Lam_mem F FC
    · nlinarith
    · nlinarith
    · nlinarith
  have hopen : ∀ j : Fin N, (∃ (n : ℕ) (ε : ℝ), 0 < ε ∧
        Lam F 0 ((t : ℝ) + 1) + ε • (vec F 1 0 - (1 / ((n : ℝ) + ((1 : ℕ) : ℝ))) • vec F 1 (-1))
          ∈ (D.tile j).carrier) →
      ∀ s u τ : ℝ, 0 < s → 0 < u → 0 < τ → τ * (s + u) < 1 →
        Lam F 0 ((t : ℝ) + 1) + τ • (s • vec F 1 0 + u • vec F 1 (-1))
          ∉ interior (D.tile j).carrier := by
    intro j ⟨n, ε, hε, hy⟩ s u τ hs hu hτ hτ1 hz
    by_cases hji : j = iG
    · subst hji
      exact ApexPlacement.not_cover_own hmG hflG (ApexPlacement.invK_pos le_rfl n) hε hy
    · have z1 := open_dir_interior (D.tile iG) mG hmG hflG hs hu hτ hτ1
      exact Set.disjoint_left.mp (D.interiors_disjoint (Ne.symm hji)) z1 hz
  obtain ⟨j, hXj, ⟨n, ε, hε, hy⟩, hcase⟩ :=
    ApexPlacement.flank_neighbour_gen D.tile _ hΔ 1 le_rfl hcovn hopen
  have hjG : j ≠ iG := by
    rintro rfl; exact ApexPlacement.not_cover_own hmG hflG (ApexPlacement.invK_pos le_rfl n) hε hy
  rcases hcase with ⟨m, hm, U', W', hUW', S, hS, hU, hside⟩ | ⟨m, -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m', hm'⟩ := hvert j hXj
    exact NearBaseVertex.vertex_not_edge (D.tile j) m' hm' m hmpos
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' j m
  rw [hm] at hang
  rcases hang with hj | hj | hj
  · rcases alpha_at F FC hm hUW' hS hU hside hj with h | h
    · refine ⟨j, ?_⟩; rw [h]; simp only [Up, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    · -- the swap lays `b` on the leg: `lem:sidenob` (m = 1)
      exfalso
      have hq : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
      have hP : Lam F 0 ((t : ℝ) + 1) ∈ Set.range (D.tile j).pts := by rw [h, Xs]; simp
      have hQ : Lam F 0 ((t : ℝ) + 1 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)
          ∈ Set.range (D.tile j).pts := by rw [h, Xs]; simp
      have hPQ : Lam F 0 ((t : ℝ) + 1) ≠ Lam F 0 ((t : ℝ) + 1 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) /
          (f : ℝ) ^ 2) := Lam_ne F FC (Or.inr (by intro h'; linarith))
      obtain ⟨m', hm'⟩ := edge_idx hP hQ hPQ
      have hleg : ∀ y : ℝ, Lam F 0 y = F.A + (y * (f : ℝ) ^ 2) • F.uL := fun y => by
        simp only [Lam, vec, v]; rw [smul_smul]; module
      have hd : dist (Lam F 0 ((t : ℝ) + 1)) (Lam F 0 ((t : ℝ) + 1 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) /
          (f : ℝ) ^ 2)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rw [dist_Lam, sub_self, show (t : ℝ) + 1 - ((t : ℝ) + 1 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) /
          (f : ℝ) ^ 2) = -(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) by ring,
          show vec F 0 (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))
            = - vec F 0 (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) by rw [vec_neg]; norm_num,
          norm_neg, norm_vec_0q F hq.le, div_mul_cancel₀ _ hc0.ne']
      rcases hm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact L.hlegnob j m' _ _ (h1.trans (hleg _)) (h2.trans (hleg _)) (by rw [h1, h2]; exact hd)
      · exact L.hlegnob j m' _ _ (h1.trans (hleg _)) (h2.trans (hleg _))
          (by rw [h1, h2, dist_comm]; exact hd)
  · exfalso
    exact ne_of_flank_lam F FC hm hUW' hS hU rB (d1 := 0) (e1 := -1) (d2 := 1) (e2 := -1)
      (by ring) (by ring) (by ring) (by ring)
      (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith)
      (eq_of_card_one cB (mem_filter_of hj) (mem_filter_of gB))
  · exact absurd (eq_of_card_one cC (mem_filter_of hj) (mem_filter_of gG)) hjG

/-! ## §3 The row line `L_x` and its right side -/

/-- The right-side chain of the row line `L_x = {col = col A + x}`: tile edges on `L_x` whose tile
lies in `{col ≥ col A + x}` (away from the leg). -/
noncomputable def rightChain (F : HFrame D e f α β γ) (x : ℝ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-(col F)) (-(col F (Lam F x 0)))

/-- `y` is straddled from the right side of `L_x`. -/
def RStr (F : HFrame D e f α β γ) (x : ℝ) (y : Plane) : Prop :=
  TraceCovering.Straddled D.toDissection (-(col F)) (-(col F (Lam F x 0))) y

theorem uL_vec : F.uL = vec F 0 (1 / (f : ℝ) ^ 2) := by
  simp only [vec, v, zero_smul, zero_add, smul_smul]
  rw [one_div_mul_cancel (cf_pos F).ne', one_smul]

theorem col_uL (FC : ApexPlacement.FrameCoords F) : col F F.uL = 0 := by
  rw [uL_vec F, col_vec F FC]

theorem Lam_line (x y : ℝ) : Lam F x y = Lam F x 0 + (y * (f : ℝ) ^ 2) • F.uL := by
  simp only [Lam, vec, v]; rw [smul_smul]; module

/-- Membership in the right chain of `L_x`. -/
theorem mem_rightChain (FC : ApexPlacement.FrameCoords F) {x y1 y2 : ℝ} {z : Fin N} {m : Fin 3}
    (h1 : (D.tile z).pts m = Lam F x y1) (h2 : (D.tile z).pts (m + 1) = Lam F x y2)
    (hall : ∀ k, col F F.A + x ≤ col F ((D.tile z).pts k)) : (z, m) ∈ rightChain F x := by
  rw [rightChain, Dissection.mem_lineChain]
  simp only [LinearMap.neg_apply, neg_inj, neg_le_neg_iff]
  refine ⟨by rw [h1, col_Lam F FC, col_Lam F FC], by rw [h2, col_Lam F FC, col_Lam F FC],
    fun k => by rw [col_Lam F FC]; exact hall k⟩

/-- **Lemma A on `L_{j+1}`** (the junction kill).  If the down cells `Dn j s`, `s < T`, line the left
side of `L_{j+1}` from `(j+1)P′` to `Λ(j+1, T)` with `c`-edges, no right-side edge passes through
`(j+1)P′`, and a right-side `b`-edge lies in `[(j+1)P′, Λ(j+1,T)]`, then `Λ(j+1, T)` is straddled from
the right: otherwise the right side of that wall is a whole-edge word of value `T·c`
(`TraceCovering.wall_sum`) containing `b`.  **m = 1 enters here**: `Inflation.c_side_no_b` needs
`T < f` (the line has fewer than `f` cells); at N = 44 (`m = 2`) `2c = a + 2b`. -/
theorem junc_kill (L : LFrame F) (j T : ℕ) (hjT : j + 1 + T ≤ f)
    (hcells : ∀ s < T, Present D (Dn F j s))
    (hstart : ¬ RStr F ((j : ℝ) + 1) (Lam F ((j : ℝ) + 1) 0))
    (hseed : ∃ ε ∈ rightChain F ((j : ℝ) + 1), ∃ s0 : ℝ, 0 ≤ s0 ∧
      s0 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 ≤ T ∧
      EdgeIs D ε (Lam F ((j : ℝ) + 1) s0)
        (Lam F ((j : ℝ) + 1) (s0 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)))
    (hend : ¬ RStr F ((j : ℝ) + 1) (Lam F ((j : ℝ) + 1) T)) : False := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hjTR : (j : ℝ) + 1 + T ≤ f := by exact_mod_cast hjT
  have hu1 : ‖F.uL‖ = 1 := F.huL
  have hu0 : F.uL ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hg : col F ≠ 0 := col_ne F FC
  have hg' : (-(col F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(col F)) y = -(col F (Lam F ((j : ℝ) + 1) 0)) ↔
      col F y = col F (Lam F ((j : ℝ) + 1) 0) := TraceCovering.neg_iff
  have hgu : col F F.uL = 0 := col_uL F FC
  have hpt : ∀ y : ℝ, Lam F ((j : ℝ) + 1) y = Lam F ((j : ℝ) + 1) 0 + (y * (f : ℝ) ^ 2) • F.uL :=
    fun y => Lam_line F _ y
  have htt0 : (0 : ℝ) ≤ (T : ℝ) * (f : ℝ) ^ 2 := by positivity
  have hint : ∀ x ∈ Set.Ioo 0 ((T : ℝ) * (f : ℝ) ^ 2),
      Lam F ((j : ℝ) + 1) 0 + x • F.uL ∈ interior D.target.carrier := by
    intro x hx
    have : Lam F ((j : ℝ) + 1) 0 + x • F.uL = Lam F ((j : ℝ) + 1) (x / (f : ℝ) ^ 2) := by
      rw [hpt (x / _), div_mul_cancel₀ _ hc0.ne']
    rw [this]
    apply Lam_interior F FC (by positivity) (div_nonneg hx.1.le hc0.le)
    have : x / (f : ℝ) ^ 2 < T := by rw [div_lt_iff₀ hc0]; exact hx.2
    linarith
  have hwall : ∀ x ∈ Set.Ioo 0 ((T : ℝ) * (f : ℝ) ^ 2), ∀ i,
      Lam F ((j : ℝ) + 1) 0 + x • F.uL ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hq0 : 0 ≤ x / (f : ℝ) ^ 2 := div_nonneg hx.1.le hc0.le
    have hk1 : ((⌊x / (f : ℝ) ^ 2⌋₊ : ℕ) : ℝ) ≤ x / (f : ℝ) ^ 2 := Nat.floor_le hq0
    have hk2 : x / (f : ℝ) ^ 2 < ((⌊x / (f : ℝ) ^ 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    set k := ⌊x / (f : ℝ) ^ 2⌋₊ with hk
    have hkx : (k : ℝ) * (f : ℝ) ^ 2 ≤ x := by rwa [le_div_iff₀ hc0] at hk1
    have hxk : x < ((k : ℝ) + 1) * (f : ℝ) ^ 2 := by rwa [div_lt_iff₀ hc0] at hk2
    have hkT : k < T := by
      have h1 : (k : ℝ) * (f : ℝ) ^ 2 < (T : ℝ) * (f : ℝ) ^ 2 := lt_of_le_of_lt hkx hx.2
      exact_mod_cast lt_of_mul_lt_mul_right h1 hc0.le
    obtain ⟨iz, hiz⟩ := hcells k hkT
    have hP : Lam F ((j : ℝ) + 1) k ∈ Set.range (D.tile iz).pts := by rw [hiz, Dn]; simp
    have hQ : Lam F ((j : ℝ) + 1) ((k : ℝ) + 1) ∈ Set.range (D.tile iz).pts := by
      rw [hiz, Dn]; simp
    have hPQ : Lam F ((j : ℝ) + 1) k ≠ Lam F ((j : ℝ) + 1) ((k : ℝ) + 1) :=
      Lam_ne F FC (Or.inr (by intro h; linarith))
    obtain ⟨m, hm⟩ := edge_idx hP hQ hPQ
    have hseg : Lam F ((j : ℝ) + 1) 0 + x • F.uL ∈
        segment ℝ (Lam F ((j : ℝ) + 1) k) (Lam F ((j : ℝ) + 1) ((k : ℝ) + 1)) := by
      rw [hpt k, hpt ((k : ℝ) + 1), TraceCovering.segment_param]
      exact ⟨x, ⟨le_trans (min_le_left _ _) hkx, le_trans hxk.le (le_max_right _ _)⟩, rfl⟩
    have hmem : Lam F ((j : ℝ) + 1) 0 + x • F.uL ∈ (D.tile iz).edge m := by
      rw [Tri.edge]
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hseg
      · rw [h1, h2, segment_symm]; exact hseg
    exact D.toDissection.edge_point_not_interior hmem i
  have hs : ¬ TraceCovering.Straddled D.toDissection (-(col F)) (-(col F (Lam F ((j : ℝ) + 1) 0)))
      (Lam F ((j : ℝ) + 1) 0 + (0 : ℝ) • F.uL) := by
    rw [zero_smul, add_zero]; exact hstart
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(col F)) (-(col F (Lam F ((j : ℝ) + 1) 0)))
      (Lam F ((j : ℝ) + 1) 0 + ((T : ℝ) * (f : ℝ) ^ 2) • F.uL) := by
    rw [← hpt]; exact hend
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg rfl hgu hu1 htt0 hint hwall
    hs ht
  -- the seed `b`-edge is one of the whole edges of the stretch
  obtain ⟨ε0, hε0, s0, hs0, hs0T, hE⟩ := hseed
  have hbc0 : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  have hpq : (D.tile ε0.1).pts ε0.2 ≠ (D.tile ε0.1).pts (ε0.2 + 1) :=
    pts_ne _ (TraceCovering.fin3_succ_ne ε0.2)
  have hseg : ∀ y : ℝ, 0 ≤ y → y ≤ (T : ℝ) → Lam F ((j : ℝ) + 1) y ∈ segment ℝ
      (Lam F ((j : ℝ) + 1) 0 + (0 : ℝ) • F.uL)
      (Lam F ((j : ℝ) + 1) 0 + ((T : ℝ) * (f : ℝ) ^ 2) • F.uL) := by
    intro y hy0 hyT
    rw [hpt y, TraceCovering.segment_param, min_eq_left htt0, max_eq_right htt0]
    exact ⟨_, ⟨by positivity, mul_le_mul_of_nonneg_right hyT hc0.le⟩, rfl⟩
  have hb1 := hseg s0 hs0 (by linarith)
  have hb2 := hseg _ (by positivity) hs0T
  have hin : (D.tile ε0.1).edge ε0.2 ⊆ segment ℝ (Lam F ((j : ℝ) + 1) 0 + (0 : ℝ) • F.uL)
      (Lam F ((j : ℝ) + 1) 0 + ((T : ℝ) * (f : ℝ) ^ 2) • F.uL) := by
    rw [Tri.edge]
    rcases pair_cases hE hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact (convex_segment _ _).segment_subset hb1 hb2
    · exact (convex_segment _ _).segment_subset hb2 hb1
  have hd : dist (Lam F ((j : ℝ) + 1) s0)
      (Lam F ((j : ℝ) + 1) (s0 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))
        = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [dist_Lam, sub_self, show s0 - (s0 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)
      = -(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) by ring,
      show vec F 0 (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2))
        = - vec F 0 (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) by rw [vec_neg]; norm_num,
      norm_neg, norm_vec_0q F hbc0.le, div_mul_cancel₀ _ hc0.ne']
  have hdM : dist ((D.tile ε0.1).pts ε0.2) ((D.tile ε0.1).pts (ε0.2 + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rcases pair_cases hE hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hd
    · rw [h1, h2, dist_comm]; exact hd
  set sF := (D.toDissection.lineChain (-(col F)) (-(col F (Lam F ((j : ℝ) + 1) 0)))).filter
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ (Lam F ((j : ℝ) + 1) 0 + (0 : ℝ) • F.uL)
      (Lam F ((j : ℝ) + 1) 0 + ((T : ℝ) * (f : ℝ) ^ 2) • F.uL)) with hsF
  have hmemS : ε0 ∈ sF := Finset.mem_filter.mpr ⟨hε0, hin⟩
  rw [← Finset.add_sum_erase sF _ hmemS] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := Erdos634.Geometry.sum_three_values (sF.erase ε0)
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
  have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
      = ((T * f ^ 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hee]
    simp only at hsum hdM
    rw [hdM] at hsum
    linarith
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = T * f ^ 2 := by
    exact_mod_cast hreal
  have := Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) T P' (Q' + 1) R' (by have := F.he; omega)
    (by have := F.hef; omega) F.hco (Nat.sub_add_cancel hee) (by omega) hnat
  omega

/-- **The base end**: `Λ(x, f − x)` lies on the base, so no edge of `L_x` passes through it. -/
theorem base_nstr (L : LFrame F) (x : ℝ) : ¬ RStr F x (Lam F x ((f : ℝ) - x)) := by
  have FC := L.FC
  obtain ⟨-, -, hc0, -, -⟩ := consts F
  rw [Lam_line F x ((f : ℝ) - x)]
  unfold RStr
  refine TraceCovering.not_straddled_of_outside_after TraceCovering.neg_iff (col_ne F FC) rfl
    (col_uL F FC) (TraceCovering.ne_zero_of_norm F.huL) (fun s hs => ?_)
  have : Lam F x 0 + s • F.uL = Lam F x (s / (f : ℝ) ^ 2) := by
    rw [Lam_line F x (s / _), div_mul_cancel₀ _ hc0.ne']
  rw [this]
  apply Lam_out F FC
  have : ((f : ℝ) - x) < s / (f : ℝ) ^ 2 := by rw [lt_div_iff₀ hc0]; exact hs
  linarith

/-- **`C(i,m)`(ii), first half: the right-side covering of `L_i` starts at `iP′`** once the up cell
`T₃ + iP′ = Up i 0` is present (its `c`-edge `[iP′, Λ(i,1)]` is a right-side edge; a right-side edge
through `iP′` would overlap it — `TraceCovering.meet`). -/
theorem start_of_up (L : LFrame F) (i : ℕ) (hU : Present D (Up F i 0)) :
    ¬ RStr F i (Lam F i 0) := by
  classical
  have FC := L.FC
  obtain ⟨-, -, hc0, -, -⟩ := consts F
  obtain ⟨iU, hrU⟩ := hU
  have hu0 : F.uL ≠ 0 := TraceCovering.ne_zero_of_norm F.huL
  have hg : col F ≠ 0 := col_ne F FC
  have hg' : (-(col F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(col F)) y = -(col F (Lam F i 0)) ↔ col F y = col F (Lam F i 0) :=
    TraceCovering.neg_iff
  have hgu : col F F.uL = 0 := col_uL F FC
  have hr : Set.range (D.tile iU).pts = {Lam F i 0, Lam F ((i : ℝ) + 1) 0, Lam F i 1} := by
    rw [hrU]; simp only [Up, Nat.cast_zero, zero_add]
  have hP : Lam F i 0 ∈ Set.range (D.tile iU).pts := by rw [hr]; simp
  have hQ : Lam F i 1 ∈ Set.range (D.tile iU).pts := by rw [hr]; simp
  obtain ⟨m, hm⟩ := edge_idx hP hQ (Lam_ne F FC (Or.inr (by norm_num)))
  have hall : ∀ k, col F F.A + i ≤ col F ((D.tile iU).pts k) := by
    intro k
    have : (D.tile iU).pts k ∈ Set.range (D.tile iU).pts := ⟨k, rfl⟩
    rw [hr] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h <;> rw [h, col_Lam F FC] <;> linarith
  have he1 : (iU, m) ∈ D.toDissection.lineChain (-(col F)) (-(col F (Lam F i 0))) := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mem_rightChain F FC h1 h2 hall
    · exact mem_rightChain F FC h1 h2 hall
  have hpt : ∀ y : ℝ, Lam F i y = Lam F i 0 + (y * (f : ℝ) ^ 2) • F.uL := fun y => Lam_line F _ y
  have hedge : (D.tile iU).edge m = segment ℝ (Lam F i 0 + (0 : ℝ) • F.uL)
      (Lam F i 0 + ((f : ℝ) ^ 2) • F.uL) := by
    have e0 : Lam F i 0 + (0 : ℝ) • F.uL = Lam F i 0 := by rw [zero_smul, add_zero]
    have e1 : Lam F i 0 + ((f : ℝ) ^ 2) • F.uL = Lam F i 1 := by rw [hpt 1, one_mul]
    rw [Tri.edge, e0, e1]
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
  have hin := fun y => TraceCovering.mem_edge_iff hgd hg rfl hgu hu0 he1 y
  have hX1 := (hin 0).mp (by rw [hedge]; exact left_mem_segment ℝ _ _)
  have hX2 := (hin ((f : ℝ) ^ 2)).mp (by rw [hedge]; exact right_mem_segment ℝ _ _)
  intro hstr
  have hstr' : TraceCovering.Straddled D.toDissection (-(col F)) (-(col F (Lam F i 0)))
      (Lam F i 0 + (0 : ℝ) • F.uL) := by rw [zero_smul, add_zero]; exact hstr
  obtain ⟨ε, hε, hlo, hhi⟩ := (TraceCovering.str_iff hgd hg rfl hgu hu0 0).mp hstr'
  by_cases hεe : ε = (iU, m)
  · subst hεe
    have hlo' := (hin (TraceCovering.lo D.toDissection (Lam F i 0) F.uL (iU, m))).mpr
      ⟨le_rfl, by linarith⟩
    rw [hedge, TraceCovering.segment_param] at hlo'
    obtain ⟨x', hx', hxe⟩ := hlo'
    have := TraceCovering.lm_injective hu0 hxe
    rw [min_eq_left hc0.le] at hx'
    linarith [hx'.1]
  · have hsub := TraceCovering.meet hg' hgd hg rfl hgu hu0 ε hε (iU, m) he1 hεe
    set δ := min (TraceCovering.hi D.toDissection (Lam F i 0) F.uL ε) ((f : ℝ) ^ 2) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hhi hc0)
    have hδ1 : δ < TraceCovering.hi D.toDissection (Lam F i 0) F.uL ε := by
      have := min_le_left (TraceCovering.hi D.toDissection (Lam F i 0) F.uL ε) ((f : ℝ) ^ 2)
      rw [hδ]; linarith
    have hδ2 : δ ≤ (f : ℝ) ^ 2 := by
      have := min_le_right (TraceCovering.hi D.toDissection (Lam F i 0) F.uL ε) ((f : ℝ) ^ 2)
      rw [hδ]; linarith
    have := hsub ⟨⟨hlo.le, hhi.le⟩, hX1⟩ ⟨⟨by linarith, hδ1.le⟩, ⟨by linarith [hX1.1], by
      linarith [hX2.2]⟩⟩
    linarith

/-- **`C(i,m)`(ii), second half: the swap's `b`-edge is a right-side edge of `L_x`.** -/
theorem seed_of_Xs (L : LFrame F) (x y : ℝ) (hX : Present D (Xs F x y)) :
    ∃ ε ∈ rightChain F x, EdgeIs D ε (Lam F x y)
      (Lam F x (y + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) := by
  have FC := L.FC
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  obtain ⟨iX, hr⟩ := hX
  have hP : Lam F x y ∈ Set.range (D.tile iX).pts := by rw [hr, Xs]; simp
  have hQ : Lam F x (y + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) ∈ Set.range (D.tile iX).pts := by
    rw [hr, Xs]; simp
  have hq : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  obtain ⟨m, hm⟩ := edge_idx hP hQ (Lam_ne F FC (Or.inr (by intro h; linarith)))
  have hall : ∀ k, col F F.A + x ≤ col F ((D.tile iX).pts k) := by
    intro k
    have : (D.tile iX).pts k ∈ Set.range (D.tile iX).pts := ⟨k, rfl⟩
    rw [hr, Xs] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    have hcb : (0 : ℝ) < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
    rcases this with h | h | h <;> rw [h, col_Lam F FC] <;> linarith
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(iX, m), mem_rightChain F FC h1 h2 hall, by simp only [EdgeIs]; rw [h1, h2]⟩
  · exact ⟨(iX, m), mem_rightChain F FC h1 h2 hall,
      by simp only [EdgeIs]; rw [h1, h2, Set.pair_comm]⟩

/-- **(A), `i = j`: the swap at the last slot dies** (`i = j − 1` in the paper, with `j+1` strips).
The swap `Xs j (T+1)` lays its `c`-edge from `Λ(j, T+1)` along `w`, through `Λ(j+1, T+1)` on `L_{j+1}`
(`b < c`); if that point is straddled from the right of `L_{j+1}`, two straight tiles meet there, and
the down cell `Dn j T` presents `α` there: impossible (`interior_card_eqs`). -/
theorem cross_kill (L : LFrame F) (j T : ℕ) (hjT : j + T + 3 ≤ f)
    (hXs : Present D (Xs F j ((T : ℝ) + 1))) (hA : Present D (Dn F j T))
    (hstr : RStr F ((j : ℝ) + 1) (Lam F ((j : ℝ) + 1) ((T : ℝ) + 1))) : False := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hR : (j : ℝ) + T + 3 ≤ f := by exact_mod_cast hjT
  have hXint : Lam F ((j : ℝ) + 1) ((T : ℝ) + 1) ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) (by positivity) (by linarith)
  obtain ⟨iA, hrA⟩ := hA
  have gA : (D.tile iA).localAngle (Lam F ((j : ℝ) + 1) ((T : ℝ) + 1)) = α := (Dn_angles F hrA).2.2
  obtain ⟨iX, hrX⟩ := hXs
  have hcb : (0 : ℝ) < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
  have hP0 : Lam F j ((T : ℝ) + 1) ∈ Set.range (D.tile iX).pts := by rw [hrX, Xs]; simp
  have hP1 : Lam F ((j : ℝ) + (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((T : ℝ) + 1)
      ∈ Set.range (D.tile iX).pts := by rw [hrX, Xs]; simp
  have hne : Lam F j ((T : ℝ) + 1) ≠
      Lam F ((j : ℝ) + (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((T : ℝ) + 1) :=
    Lam_ne F FC (Or.inl (by intro h; linarith))
  obtain ⟨m, hm⟩ := edge_idx hP0 hP1 hne
  set lam : ℝ := ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam < 1 := by rw [hlam, div_lt_one hc0]; linarith
  have hopen : Lam F ((j : ℝ) + 1) ((T : ℝ) + 1) ∈ openSegment ℝ (Lam F j ((T : ℝ) + 1))
      (Lam F ((j : ℝ) + (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ((T : ℝ) + 1)) := by
    refine ⟨1 - lam, lam, by linarith, hlam0, by ring, ?_⟩
    have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
    have hk : (j : ℝ) + 1 = j + lam * ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
      rw [hlam]; field_simp
    rw [hk]; simp only [Lam, vec]; module
  have hx : Lam F ((j : ℝ) + 1) ((T : ℝ) + 1) ∈
      openSegment ℝ ((D.tile iX).pts m) ((D.tile iX).pts (m + 1)) := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hopen
    · rw [h1, h2, openSegment_symm]; exact hopen
  have sX := straight_count hx
  obtain ⟨ε, hε, hxε⟩ := hstr
  have sε := straight_count hxε
  have hne' : iX ≠ ε.1 := by
    intro heq
    rw [heq] at hx hm
    have hme := Level2LemmaGReal.same_edge (D.tile ε.1) hx hxε
    rw [hme] at hm
    obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε
    simp only [LinearMap.neg_apply, neg_inj] at h0 h1
    rw [col_Lam F FC] at h0 h1
    rcases hm with ⟨e1, -⟩ | ⟨-, e2⟩
    · rw [e1, col_Lam F FC] at h0; linarith
    · rw [e2, col_Lam F FC] at h1; linarith
  have h2 := Level2LemmaGReal.two_straight hne' sX sε
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
  have := card_one gA
  omega

/-! ## §4 (B) the next row -/

/-- The lower-side chain of row `n = {lev = lev A + n}`: edges on the row whose tile lies in
`{lev ≥ lev A + n}` (away from `A`). -/
noncomputable def rowChain (F : HFrame D e f α β γ) (n : ℝ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-(lev F)) (-(lev F F.A + n))

theorem mem_rowChain {n : ℝ} {z : Fin N} {m : Fin 3}
    (h1 : lev F ((D.tile z).pts m) = lev F F.A + n)
    (h2 : lev F ((D.tile z).pts (m + 1)) = lev F F.A + n)
    (hall : ∀ k, lev F F.A + n ≤ lev F ((D.tile z).pts k)) : (z, m) ∈ rowChain F n := by
  rw [rowChain, Dissection.mem_lineChain]
  simp only [LinearMap.neg_apply, neg_inj, neg_le_neg_iff]
  exact ⟨h1, h2, hall⟩

/-- **(B), the row word.**  Row `n = j + d + 2` from `X₀ = Λ(j+1, d+1)` to the leg point `J_n` is a
wall (the `a`-edges of the band-`B_{n−1}` up cells), `X₀` is not straddled from below (the right
straddler of `L_{j+1}` and the `α` of `Dn j d` leave no room for a second straight tile), `J_n` is on
the leg; so its lower side is a whole-edge word of value `(j+1)·a` (`TraceCovering.wall_sum`), and
by **m = 1** (`Inflation.a_side_no_b`, `a_side_rigid`, `j + 1 < f`; at N = 44, `2a = c`) every lower
edge in it is an `a`-edge.  Stated for a lower edge leaving a row point `Λ(p,q)` along the row. -/
theorem row_all_a (L : LFrame F) (j d : ℕ) (hjd : j + d + 3 ≤ f)
    (hUp : ∀ i t, i ≤ j → i + t = j + 1 + d → Present D (Up F i t))
    (hDn : ∀ i t, i ≤ j → i + t = j + d → Present D (Dn F i t))
    (hstr : RStr F ((j : ℝ) + 1) (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1))) :
    ∀ ε ∈ rowChain F ((j : ℝ) + d + 2), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (j : ℝ) + 1 →
      p + q = (j : ℝ) + d + 2 →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hR : (j : ℝ) + d + 3 ≤ f := by exact_mod_cast hjd
  have hur1 : ‖(1 / ((e : ℝ) * f)) • vec F (-1) 1‖ = 1 := by
    rw [norm_smul, norm_vec_m11, Real.norm_of_nonneg (by positivity), one_div_mul_cancel ha0.ne']
  have hur0 := TraceCovering.ne_zero_of_norm hur1
  have hlev_ur : lev F ((1 / ((e : ℝ) * f)) • vec F (-1) 1) = 0 := by
    rw [map_smul, lev_vec F FC]; simp
  have hg : lev F ≠ 0 := lev_ne F FC
  have hg' : (-(lev F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(lev F)) y = -(lev F F.A + ((j : ℝ) + d + 2)) ↔
      lev F y = lev F F.A + ((j : ℝ) + d + 2) := TraceCovering.neg_iff
  have hX : lev F (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1)) = lev F F.A + ((j : ℝ) + d + 2) := by
    rw [lev_Lam F FC]; ring
  have hrow : ∀ x : ℝ, Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
      = Lam F ((j : ℝ) + 1 - x / ((e : ℝ) * f)) ((d : ℝ) + 1 + x / ((e : ℝ) * f)) := by
    intro x
    rw [smul_smul, vec_smul]
    apply Lam_add_eq F <;> ring
  have hst : (0 : ℝ) ≤ ((j : ℝ) + 1) * ((e : ℝ) * f) := by positivity
  have hint : ∀ x ∈ Set.Ioo 0 (((j : ℝ) + 1) * ((e : ℝ) * f)),
      Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
        ∈ interior D.target.carrier := by
    intro x hx
    rw [hrow]
    have h1 : x / ((e : ℝ) * f) < (j : ℝ) + 1 := by rw [div_lt_iff₀ ha0]; exact hx.2
    have h2 : 0 ≤ x / ((e : ℝ) * f) := div_nonneg hx.1.le ha0.le
    exact Lam_interior F FC (by linarith) (by positivity) (by linarith)
  have hwall : ∀ x ∈ Set.Ioo 0 (((j : ℝ) + 1) * ((e : ℝ) * f)), ∀ i,
      Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
        ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hq0 : 0 ≤ x / ((e : ℝ) * f) := div_nonneg hx.1.le ha0.le
    have hk1 : ((⌊x / ((e : ℝ) * f)⌋₊ : ℕ) : ℝ) ≤ x / ((e : ℝ) * f) := Nat.floor_le hq0
    have hk2 : x / ((e : ℝ) * f) < ((⌊x / ((e : ℝ) * f)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    set k := ⌊x / ((e : ℝ) * f)⌋₊ with hk
    have hkx : (k : ℝ) * ((e : ℝ) * f) ≤ x := by rwa [le_div_iff₀ ha0] at hk1
    have hxk : x < ((k : ℝ) + 1) * ((e : ℝ) * f) := by rwa [div_lt_iff₀ ha0] at hk2
    have hkj : k ≤ j := by
      have h1 : (k : ℝ) * ((e : ℝ) * f) < ((j : ℝ) + 1) * ((e : ℝ) * f) := lt_of_le_of_lt hkx hx.2
      have h2 : (k : ℝ) < (j : ℝ) + 1 := lt_of_mul_lt_mul_right h1 ha0.le
      have h3 : k < j + 1 := by exact_mod_cast h2
      omega
    obtain ⟨i', hi'⟩ : ∃ i', i' + k = j := ⟨j - k, by omega⟩
    have hi'R : (i' : ℝ) = (j : ℝ) - k := by
      have : ((i' + k : ℕ) : ℝ) = j := by exact_mod_cast hi'
      push_cast at this; linarith
    obtain ⟨iz, hiz⟩ := hUp i' (d + 1 + k) (by omega) (by omega)
    have hP : Lam F ((i' : ℝ) + 1) ((d + 1 + k : ℕ) : ℝ) ∈ Set.range (D.tile iz).pts := by
      rw [hiz, Up]; simp
    have hQ : Lam F (i' : ℝ) (((d + 1 + k : ℕ) : ℝ) + 1) ∈ Set.range (D.tile iz).pts := by
      rw [hiz, Up]; simp
    have hPQ : Lam F ((i' : ℝ) + 1) ((d + 1 + k : ℕ) : ℝ) ≠ Lam F (i' : ℝ) (((d + 1 + k : ℕ) : ℝ) + 1) :=
      Lam_ne F FC (Or.inl (by intro h; linarith))
    obtain ⟨m, hm⟩ := edge_idx hP hQ hPQ
    have e1 : Lam F ((i' : ℝ) + 1) ((d + 1 + k : ℕ) : ℝ) = Lam F ((j : ℝ) + 1) ((d : ℝ) + 1)
        + ((k : ℝ) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
      rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
      · linarith
      · push_cast; ring
    have e2 : Lam F (i' : ℝ) (((d + 1 + k : ℕ) : ℝ) + 1) = Lam F ((j : ℝ) + 1) ((d : ℝ) + 1)
        + (((k : ℝ) + 1) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
      rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
      · linarith
      · push_cast; ring
    have hseg : Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) ∈
        segment ℝ (Lam F ((i' : ℝ) + 1) ((d + 1 + k : ℕ) : ℝ))
          (Lam F (i' : ℝ) (((d + 1 + k : ℕ) : ℝ) + 1)) := by
      rw [e1, e2, TraceCovering.segment_param]
      exact ⟨x, ⟨le_trans (min_le_left _ _) hkx, le_trans hxk.le (le_max_right _ _)⟩, rfl⟩
    have hmem : Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
        ∈ (D.tile iz).edge m := by
      rw [Tri.edge]
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hseg
      · rw [h1, h2, segment_symm]; exact hseg
    exact D.toDissection.edge_point_not_interior hmem i
  -- `X₀` is not straddled from below
  have hXint : Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) (by positivity) (by linarith)
  have hs : ¬ TraceCovering.Straddled D.toDissection (-(lev F)) (-(lev F F.A + ((j : ℝ) + d + 2)))
      (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
    rw [zero_smul, add_zero]
    rintro ⟨ε, hε, hxε⟩
    obtain ⟨ε', hε', hxε'⟩ := hstr
    have s1 := straight_count hxε
    have s2 := straight_count hxε'
    obtain ⟨iA, hrA⟩ := hDn j d le_rfl rfl
    have gA : (D.tile iA).localAngle (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1)) = α := (Dn_angles F hrA).2.2
    obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hXint
    have cA := card_one gA
    by_cases heq : ε.1 = ε'.1
    · rw [← heq] at hxε'
      have hme := Level2LemmaGReal.same_edge (D.tile ε.1) hxε hxε'
      obtain ⟨a0, a1, -⟩ := Dissection.mem_lineChain.mp hε
      obtain ⟨b0, b1, -⟩ := Dissection.mem_lineChain.mp hε'
      simp only [LinearMap.neg_apply, neg_inj] at a0 a1 b0 b1
      rw [← heq, ← hme] at b0 b1
      exact pts_ne _ (TraceCovering.fin3_succ_ne ε.2)
        (eq_of_col_lev F FC (b0.trans b1.symm) (a0.trans a1.symm))
    · have := Level2LemmaGReal.two_straight heq s1 s2
      omega
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(lev F)) (-(lev F F.A + ((j : ℝ) + d + 2)))
      (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (((j : ℝ) + 1) * ((e : ℝ) * f)) •
        ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
    refine TraceCovering.not_straddled_of_outside_after hgd hg hX hlev_ur hur0 (fun s hs => ?_)
    rw [hrow]
    apply Lam_neg F FC
    have : (j : ℝ) + 1 < s / ((e : ℝ) * f) := by rw [lt_div_iff₀ ha0]; exact hs
    linarith
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg hX hlev_ur hur1 hst hint hwall
    hs ht
  -- the given edge
  intro ε hε p q ℓ hℓ hp hpq hE
  have hpq' : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
    pts_ne _ (TraceCovering.fin3_succ_ne ε.2)
  have hPe : Lam F p q = Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) +
      ((((j : ℝ) + 1) - p) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
    rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
    · ring
    · linarith
  have hQe : Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f)) =
      Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + ((((j : ℝ) + 1) - p) * ((e : ℝ) * f) + ℓ) •
        ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
    rw [hrow, add_div, mul_div_cancel_right₀ _ ha0.ne']; congr 1
    · ring
    · linarith
  by_cases hin : (((j : ℝ) + 1) - p) * ((e : ℝ) * f) + ℓ ≤ ((j : ℝ) + 1) * ((e : ℝ) * f)
  · have hx0 : 0 ≤ (((j : ℝ) + 1) - p) * ((e : ℝ) * f) := mul_nonneg (by linarith) ha0.le
    have hseg : ∀ x, 0 ≤ x → x ≤ ((j : ℝ) + 1) * ((e : ℝ) * f) →
        Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) ∈
          segment ℝ (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1))
            (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (((j : ℝ) + 1) * ((e : ℝ) * f)) •
              ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
      intro x hx0 hx1
      rw [TraceCovering.segment_param, min_eq_left hst, max_eq_right hst]
      exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have hb1 := hseg _ hx0 (by linarith)
    have hb2 := hseg _ (by linarith) hin
    rw [← hPe] at hb1
    rw [← hQe] at hb2
    have hsub : (D.tile ε.1).edge ε.2 ⊆ segment ℝ
        (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1))
        (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (((j : ℝ) + 1) * ((e : ℝ) * f)) •
          ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
      rw [Tri.edge]
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact (convex_segment _ _).segment_subset hb1 hb2
      · exact (convex_segment _ _).segment_subset hb2 hb1
    have hd : dist (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) = ℓ := by
      rw [hPe, hQe, TraceCovering.dist_param hur1, max_eq_right (by linarith),
        min_eq_left (by linarith)]; ring
    have hdM : dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = ℓ := by
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hd
      · rw [h1, h2, dist_comm]; exact hd
    set sF := (D.toDissection.lineChain (-(lev F)) (-(lev F F.A + ((j : ℝ) + d + 2)))).filter
      (fun ε' => (D.tile ε'.1).edge ε'.2 ⊆ segment ℝ
        (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1))
        (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1) + (((j : ℝ) + 1) * ((e : ℝ) * f)) •
          ((1 / ((e : ℝ) * f)) • vec F (-1) 1))) with hsF
    have hmemS : ε ∈ sF := Finset.mem_filter.mpr ⟨hε, hsub⟩
    rw [← Finset.add_sum_erase sF _ hmemS] at hsum
    obtain ⟨P', Q', R', hPQR, -⟩ := Erdos634.Geometry.sum_three_values (sF.erase ε)
      (fun ε' => dist ((D.tile ε'.1).pts ε'.2) ((D.tile ε'.1).pts (ε'.2 + 1)))
      ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
      (fun ε _ => edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
    simp only at hsum hdM
    rw [hdM] at hsum
    have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
    have hb' : f ^ 2 - e ^ 2 + e ^ 2 = f ^ 2 := Nat.sub_add_cancel hee
    rcases edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2 with h | h | h <;> rw [hdM] at h
    · exact h
    · exfalso
      have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
          = (((j + 1) * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = (j + 1) * (e * f) := by
        exact_mod_cast hreal
      have := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) (j + 1) P' (Q' + 1) R'
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      omega
    · exfalso
      have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
          = (((j + 1) * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = (j + 1) * (e * f) := by
        exact_mod_cast hreal
      have hQ0 := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) (j + 1) P' Q' (R' + 1)
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      rw [hQ0, zero_mul, add_zero] at hnat
      have := Inflation.a_side_rigid e f (j + 1) P' (R' + 1) (by have := F.he; omega)
        (by have := F.hef; omega) F.hco (by omega) hnat
      omega
  · -- the edge would end beyond the leg: outside the target
    exfalso
    have hmem : Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f)) ∈ D.target.carrier := by
      have : Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f)) ∈
          ({(D.tile ε.1).pts ε.2, (D.tile ε.1).pts (ε.2 + 1)} : Set Plane) := by
        rw [hE]; simp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h <;> rw [h] <;> exact MarchInduction.pts_mem_target D.toDissection _ _
    refine Lam_neg F FC ?_ _ hmem
    push Not at hin
    have : p * ((e : ℝ) * f) < ℓ := by nlinarith
    have : p < ℓ / ((e : ℝ) * f) := by rw [lt_div_iff₀ ha0]; linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- **(B), one junction of the new row.**  At `Y = Λ(i+1, t+1)` on row `j+d+2` (`i ≤ j`), the up cell
`Up i (t+1)` presents `γ` with flank `vec(−1,1)` along the row; the tile across that flank is a
corner tile with an edge on the row (no straight tile fits: `interior_card_eqs`, with the right
straddler of `L_{j+1}` at `i = j` or the half-turn `Dn (i+1) t` already found), its row edge is an
`a`-edge (`row_all_a`), it is not `γ` (the `γ`'s are counted) nor `α` (flanks `b, c`), so it is the
`β`-tile with `c` down `L_{i+1}`: the half-turn `Dn i (t+1)` (PROP). -/
theorem row_one (L : LFrame F) (j d i t : ℕ) (hi : i ≤ j) (hit : i + (t + 1) = j + 1 + d)
    (hjd : j + d + 3 ≤ f)
    (hall : ∀ ε ∈ rowChain F ((j : ℝ) + d + 2), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (j : ℝ) + 1 →
      p + q = (j : ℝ) + d + 2 →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    (hγ : Present D (Up F i (t + 1))) (hα : Present D (Dn F i t))
    (hcase : (i = j ∧ RStr F ((j : ℝ) + 1) (Lam F ((j : ℝ) + 1) ((t : ℝ) + 1))) ∨
      Present D (Dn F (i + 1) t)) :
    Present D (Dn F i (t + 1)) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hK := K_ne F FC
  have hK2 := mul_self_pos.mpr hK
  have hitR : (i : ℝ) + ((t : ℝ) + 1) = j + 1 + d := by exact_mod_cast hit
  have hR : (j : ℝ) + d + 3 ≤ f := by exact_mod_cast hjd
  have hij : (i : ℝ) ≤ j := by exact_mod_cast hi
  have hYint : Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) (by positivity) (by linarith)
  obtain ⟨iG, hrG⟩ := hγ
  obtain ⟨iA, hrA⟩ := hα
  have gG : (D.tile iG).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
    have := (Up_angles F hrG).2.1; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
  have gA : (D.tile iA).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = α := (Dn_angles F hrA).2.2
  have rG : Set.range (D.tile iG).pts = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1),
      Lam F i ((t : ℝ) + 1 + 1), Lam F i ((t : ℝ) + 1)} := by
    rw [hrG]; simp only [Up, Nat.cast_add, Nat.cast_one]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG
  rw [Lam_sub_eq F (by ring : (i : ℝ) - ((i : ℝ) + 1) = -1)
      (by ring : ((t : ℝ) + 1 + 1) - ((t : ℝ) + 1) = 1),
    Lam_sub_eq F (by ring : (i : ℝ) - ((i : ℝ) + 1) = -1)
      (by ring : ((t : ℝ) + 1) - ((t : ℝ) + 1) = 0)] at hflG
  obtain ⟨z, hzG, hYz, hcz⟩ := flank_neighbour_dissection D.toDissection hYint hmG hflG
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hYint
  have cA := card_one gA
  have cG := card_one gG
  have hcolU : col F (vec F (-1) 1) ≠ 0 := by rw [col_vec F FC]; norm_num
  -- the γ-exclusion and the straight-tile exclusion, by case
  have hγz : ∀ z' : Fin N, z' ≠ iG → (∀ (mz : Fin 3) (U W : Plane) (S : ℝ),
      (D.tile z').pts mz = Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) →
      IsFlankPair (D.tile z') mz (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) U W → 0 < S →
      vec F (-1) 1 = S • U → (D.tile z').localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) ≠ γ) := by
    intro z' hz'G mz U W S hmz hUW hS hU0 hz'γ
    rcases hcase with ⟨rfl, ε', hε', hxε'⟩ | ⟨iG2, hrG2⟩
    · have sε := straight_count hxε'
      have := card_two hz'G hz'γ gG
      rcases sε with h | h <;> (have := card_one h; omega)
    · have gG2 : (D.tile iG2).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
        have := (Dn_angles F hrG2).2.1; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
      have rG2 : Set.range (D.tile iG2).pts = {Lam F ((i : ℝ) + 1) ((t : ℝ) + 1),
          Lam F ((i : ℝ) + 1 + 1) t, Lam F ((i : ℝ) + 1 + 1) ((t : ℝ) + 1)} := by
        rw [hrG2]; simp only [Dn, Nat.cast_add, Nat.cast_one]
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      have hG12 : iG ≠ iG2 := ne_of_range rG rG2 (p := Lam F i ((t : ℝ) + 1)) mem3_3
        (not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
          (Or.inl (by intro h; linarith)))
      have cG2 := card_two hG12 gG gG2
      rcases mem_of_card_two hG12 gG gG2 (by omega) hz'γ with h | h
      · exact hz'G h
      · exact ne_of_flank_lam F FC hmz hUW hS hU0 rG2 (d1 := 1) (e1 := -1) (d2 := 1) (e2 := 0)
          (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by linarith)
          (fun S' hS' h1 h2 => by linarith) h
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', -, hmpos, hcr, -⟩
  swap
  · -- edge case: a straight tile through `Y` along the row
    exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m' hmpos
    have hzs := localAngle_mem_pi_of_mem (D.tile z) hYz hznv
    rcases hcase with ⟨rfl, ε', hε', hxε'⟩ | ⟨iG2, hrG2⟩
    · have sε := straight_count hxε'
      by_cases hze : z = ε'.1
      · rw [← hze] at hxε'
        obtain ⟨c2, -, -⟩ := openSeg_coords (D.tile z) ε'.2 hxε'
        have hm : m' = ε'.2 + 2 := by
          by_contra hne
          have := hmpos (ε'.2 + 2) (Ne.symm hne)
          linarith
        subst hm
        rw [fin3_add_two_add_two, fin3_add_two_add_one] at hcr
        obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
        simp only [LinearMap.neg_apply, neg_inj] at h0 h1
        rw [← hze] at h0 h1
        have hd0 := sub_ne_zero.mpr (pts_ne (D.tile z) (TraceCovering.fin3_succ_ne ε'.2)).symm
        have hgd : col F ((D.tile z).pts (ε'.2 + 1) - (D.tile z).pts ε'.2) = 0 := by
          rw [map_sub]; linarith
        exact cross_ne_of_g (col F) hd0 hgd hcolU hcr
      · have := Level2LemmaGReal.two_straight hze hzs sε
        omega
    · have gG2 : (D.tile iG2).localAngle (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = γ := by
        have := (Dn_angles F hrG2).2.1; simp only [Nat.cast_add, Nat.cast_one] at this; exact this
      have hne : iG ≠ iG2 := by
        intro h
        have h1 : Lam F i ((t : ℝ) + 1) ∈ Set.range (D.tile iG).pts := by rw [rG]; exact mem3_3
        rw [h, hrG2] at h1
        simp only [Dn, Nat.cast_add, Nat.cast_one] at h1
        exact not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
          (Or.inl (by intro h; linarith)) h1
      have := card_two hne gG gG2
      rcases hzs with h | h <;> (have := card_one h; omega)
  -- vertex case: the row edge of `z`
  have hU0n : ‖vec F (-1) 1‖ = (e : ℝ) * f := norm_vec_m11 F
  have hUne : U ≠ 0 := by
    intro h; rw [h, smul_zero] at hU0; rw [hU0, norm_zero] at hU0n; linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ‖U‖ = ℓ := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := hℓdef ▸ norm_pos_iff.mpr hUne
  have hUe : U = (ℓ / ((e : ℝ) * f)) • vec F (-1) 1 := flank_eq hS hU0 hℓdef hU0n ha0
  have hlevU : lev F U = 0 := by
    have := congrArg (lev F) hU0
    rw [map_smul, lev_vec F FC, smul_eq_mul] at this
    rcases mul_eq_zero.mp (by linarith : S * lev F U = 0) with h | h
    · linarith
    · exact h
  have hlevW : 0 < lev F W := by
    have hW := vec_coords F FC W
    rw [hW, cross_vec, cross_vec] at hside
    rw [hW, lev_vec F FC]
    nlinarith
  have hY : lev F (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1)) = lev F F.A + ((j : ℝ) + d + 2) := by
    rw [lev_Lam F FC]; linarith
  have hall3 : ∀ k, lev F F.A + ((j : ℝ) + d + 2) ≤ lev F ((D.tile z).pts k) := by
    intro k
    have hk : (D.tile z).pts k ∈ Set.range (D.tile z).pts := ⟨k, rfl⟩
    rw [ApexPlacement.range_of_flank hmz hUW] at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h <;> rw [h]
    · rw [hY]
    · rw [map_add, hY, hlevU, add_zero]
    · rw [map_add, hY]; linarith
  -- the row edge `[Y, Y + U]` is a lower-side edge of the row
  obtain ⟨idx, hidx, hE⟩ : ∃ idx : Fin 3, (z, idx) ∈ rowChain F ((j : ℝ) + d + 2) ∧
      EdgeIs D (z, idx) (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1))
        (Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) + U) := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · have e1 : (D.tile z).pts (mz + 1) = Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) + U := by
        rw [h1]; abel
      refine ⟨mz, mem_rowChain F (by rw [hmz, hY]) (by rw [e1, map_add, hY, hlevU, add_zero])
        hall3, ?_⟩
      simp only [EdgeIs]; rw [hmz, e1]
    · have e1 : (D.tile z).pts (mz + 2) = Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) + U := by
        rw [h1]; abel
      have e2 : (D.tile z).pts (mz + 2 + 1) = Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) := by
        rw [fin3_add_two_add_one]; exact hmz
      refine ⟨mz + 2, mem_rowChain F (by rw [e1, map_add, hY, hlevU, add_zero])
        (by rw [e2, hY]) hall3, ?_⟩
      simp only [EdgeIs]; rw [e1, e2, Set.pair_comm]
  have hUlam : Lam F ((i : ℝ) + 1) ((t : ℝ) + 1) + U = Lam F ((i : ℝ) + 1 - ℓ / ((e : ℝ) * f))
      ((t : ℝ) + 1 + ℓ / ((e : ℝ) * f)) := by
    rw [hUe, vec_smul]; apply Lam_add_eq F <;> ring
  rw [hUlam] at hE
  have hla := hall (z, idx) hidx _ _ _ hℓ (by linarith) (by linarith) hE
  -- so `U = vec(−1,1)`, and `z` is the `β`-tile
  have hU1 : U = vec F (-1) 1 := by rw [hUe, hla, div_self ha0.ne', one_smul]
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · exfalso
    obtain ⟨hn, -⟩ := (corner_dataH F hmz hUW).2 hz
    rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hℓdef, hla] at h1; exact hab h1
    · rw [hℓdef, hla] at h1; exact hac' h1
  · obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).1 hz
    have hWc : ‖W‖ = (f : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hac'
    have hs2 : cross (vec F (-1) 1) (vec F 0 1) * cross (vec F (-1) 1) (vec F (-1) 0) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU1 (by intro h; rw [h, norm_zero] at hU0n; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU1] at this)
      (by rw [hWc, norm_vec_01]) (by rw [hopp, dist_add_vec, show (-1 : ℝ) - 0 = -1 by ring,
        show (1 : ℝ) - 1 = 0 by ring, norm_vec_m10])
    refine ⟨z, ?_⟩
    rw [hr, Lam_add_eq F (show (i : ℝ) + 1 + -1 = i by ring) rfl,
      Lam_add_eq F (add_zero _) rfl]
    simp only [Dn, Nat.cast_add, Nat.cast_one]
  · exact absurd hz (hγz z hzG mz U W S hmz hUW hS hU0)

/-- **(B), the whole row: `C(j+1, m) ⇒` the band-`B_{m+1}` down cells** (`m = j + 1 + d`), by a
descending induction along the row from `X₀ = Λ(j+1, d+1)` (`row_one`), with the row word
`row_all_a`. -/
theorem row_step (L : LFrame F) (j d : ℕ) (hjd : j + d + 3 ≤ f)
    (hUp : ∀ i t, i ≤ j → i + t = j + 1 + d → Present D (Up F i t))
    (hDn : ∀ i t, i ≤ j → i + t = j + d → Present D (Dn F i t))
    (hstr : RStr F ((j : ℝ) + 1) (Lam F ((j : ℝ) + 1) ((d : ℝ) + 1))) :
    ∀ i t, i ≤ j → i + t = j + 1 + d → Present D (Dn F i t) := by
  have hall := row_all_a F L j d hjd hUp hDn hstr
  have key : ∀ n, ∀ i, i + n = j → Present D (Dn F i (d + 1 + n)) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hij : i = j := by omega
      subst hij
      exact row_one F L i d i d le_rfl (by omega) hjd hall (hUp i (d + 1) le_rfl (by omega))
        (hDn i d le_rfl rfl) (Or.inl ⟨rfl, hstr⟩)
    | succ n ih =>
      intro i hi
      exact row_one F L j d i (d + 1 + n) (by omega) (by omega) hjd hall
        (hUp i (d + 1 + n + 1) (by omega) (by omega)) (hDn i (d + 1 + n) (by omega) (by omega))
        (Or.inr (ih (i + 1) (by omega)))
  intro i t hi hit
  have ht : t = d + 1 + (j - i) := by omega
  rw [ht]; exact key (j - i) i (by omega)

end Erdos634.Draft.RowWallReal
