-- Draft/MirrorLevelQReal.lean — PK·a (the level-q mirror `N_q` is impossible given the column
-- `T₂ + jP′`, `j < q`), for REAL `m = 1` dissections in the apex frame.  Statement of record:
-- (private working notes, not included) S2, proof_H_empty.md §5.7; reviews review_S1/REVIEW.md,
-- review2_RW/REVIEW.md.  Generalizes R2 (`q = 1`, Draft/MirrorStripR2Real.lean).
-- Imported into All.lean (Erdos634/All.lean:423), Draft/LemmaGRowReal.lean:10, Draft/IntegrationTest.lean:30.
--
-- Build (scratch oleans; never .lake): RowWallInduction olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/MirrorLevelQReal.lean'
--
-- Proof (the paper's three steps): (1) the matched ray `m₀ = A + ℝ·w` from `A` to `qP′` is a wall
-- (right side: the column's `b`-edges; `qP′` is not straddled from the left since `N_q`'s interior
-- reaches `m₀` just past `qP′`), so its left side is `b^q` (`Inflation.b_side_rigid`, **m = 1**:
-- `q < f`; at N = 44, `3b = a + c`) — `matched_word`; (2) the triangle `q·T₃` is forced row by row
-- (`row_all_gen`/`row_one_gen` for the down cells, `slot_leg`/`slot_int` for the up cells with
-- `RW(i)` killing interior swaps, `matched_slot` at `nP′`); (3) at `qP′` three `γ`'s, the row-`q`
-- down cells, and `N_q`'s `b`-edge on `L_q` give `C(q, q)`, which `RW(q)` (`rw_frame`) kills.
import Erdos634.Draft.RowWallInduction

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 The row step with a general right end (for the rows of `q·T₃`) -/

set_option maxHeartbeats 1000000 in
/-- **The row word, general right end** (`row_all_a` with the row end `Λ(J, T)` and its
non-straddle abstracted): row `J + T` from `Λ(J, T)` to the leg is a wall (the `a`-edges of the up
cells `Up i t`, `i < J`), so its lower side is a whole-edge word of value `J·a`, all `a` by
**m = 1** (`Inflation.a_side_no_b`, `a_side_rigid`, `J < f`; at N = 44, `2a = c`). -/
theorem row_all_gen (L : LFrame F) (J T : ℕ) (hJ : 1 ≤ J) (hjd : J + T + 1 ≤ f)
    (hUp : ∀ i t, i < J → i + t + 1 = J + T → Present D (Up F i t))
    (hs0 : ¬ TraceCovering.Straddled D.toDissection (-(lev F)) (-(lev F F.A + ((J : ℝ) + T)))
      (Lam F (J : ℝ) (T : ℝ))) :
    ∀ ε ∈ rowChain F ((J : ℝ) + T), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (J : ℝ) →
      p + q = (J : ℝ) + T →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hR : (J : ℝ) + T + 1 ≤ f := by exact_mod_cast hjd
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hur1 : ‖(1 / ((e : ℝ) * f)) • vec F (-1) 1‖ = 1 := by
    rw [norm_smul, norm_vec_m11, Real.norm_of_nonneg (by positivity), one_div_mul_cancel ha0.ne']
  have hur0 := TraceCovering.ne_zero_of_norm hur1
  have hlev_ur : lev F ((1 / ((e : ℝ) * f)) • vec F (-1) 1) = 0 := by
    rw [map_smul, lev_vec F FC]; simp
  have hg : lev F ≠ 0 := lev_ne F FC
  have hg' : (-(lev F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(lev F)) y = -(lev F F.A + ((J : ℝ) + T)) ↔
      lev F y = lev F F.A + ((J : ℝ) + T) := TraceCovering.neg_iff
  have hX : lev F (Lam F (J : ℝ) (T : ℝ)) = lev F F.A + ((J : ℝ) + T) := by
    rw [lev_Lam F FC]
  have hrow : ∀ x : ℝ, Lam F (J : ℝ) (T : ℝ) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
      = Lam F ((J : ℝ) - x / ((e : ℝ) * f)) ((T : ℝ) + x / ((e : ℝ) * f)) := by
    intro x
    rw [smul_smul, vec_smul]
    apply Lam_add_eq F <;> ring
  have hst : (0 : ℝ) ≤ (J : ℝ) * ((e : ℝ) * f) := by positivity
  have hint : ∀ x ∈ Set.Ioo 0 ((J : ℝ) * ((e : ℝ) * f)),
      Lam F (J : ℝ) (T : ℝ) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
        ∈ interior D.target.carrier := by
    intro x hx
    rw [hrow]
    have h1 : x / ((e : ℝ) * f) < (J : ℝ) := by rw [div_lt_iff₀ ha0]; exact hx.2
    have h2 : 0 ≤ x / ((e : ℝ) * f) := div_nonneg hx.1.le ha0.le
    exact Lam_interior F FC (by linarith) (by positivity) (by linarith)
  have hwall : ∀ x ∈ Set.Ioo 0 ((J : ℝ) * ((e : ℝ) * f)), ∀ i,
      Lam F (J : ℝ) (T : ℝ) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
        ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hq0 : 0 ≤ x / ((e : ℝ) * f) := div_nonneg hx.1.le ha0.le
    have hk1 : ((⌊x / ((e : ℝ) * f)⌋₊ : ℕ) : ℝ) ≤ x / ((e : ℝ) * f) := Nat.floor_le hq0
    have hk2 : x / ((e : ℝ) * f) < ((⌊x / ((e : ℝ) * f)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    set k := ⌊x / ((e : ℝ) * f)⌋₊ with hk
    have hkx : (k : ℝ) * ((e : ℝ) * f) ≤ x := by rwa [le_div_iff₀ ha0] at hk1
    have hxk : x < ((k : ℝ) + 1) * ((e : ℝ) * f) := by rwa [div_lt_iff₀ ha0] at hk2
    have hkj : k < J := by
      have h1 : (k : ℝ) * ((e : ℝ) * f) < (J : ℝ) * ((e : ℝ) * f) := lt_of_le_of_lt hkx hx.2
      have h2 : (k : ℝ) < (J : ℝ) := lt_of_mul_lt_mul_right h1 ha0.le
      exact_mod_cast h2
    obtain ⟨i', hi'⟩ : ∃ i', i' + k + 1 = J := ⟨J - k - 1, by omega⟩
    have hi'R : (i' : ℝ) = (J : ℝ) - k - 1 := by
      have : ((i' + k + 1 : ℕ) : ℝ) = J := by exact_mod_cast hi'
      push_cast at this; linarith
    obtain ⟨iz, hiz⟩ := hUp i' (T + k) (by omega) (by omega)
    have hP : Lam F ((i' : ℝ) + 1) ((T + k : ℕ) : ℝ) ∈ Set.range (D.tile iz).pts := by
      rw [hiz, Up]; simp
    have hQ : Lam F (i' : ℝ) (((T + k : ℕ) : ℝ) + 1) ∈ Set.range (D.tile iz).pts := by
      rw [hiz, Up]; simp
    have hPQ : Lam F ((i' : ℝ) + 1) ((T + k : ℕ) : ℝ) ≠ Lam F (i' : ℝ) (((T + k : ℕ) : ℝ) + 1) :=
      Lam_ne F FC (Or.inl (by intro h; linarith))
    obtain ⟨m, hm⟩ := edge_idx hP hQ hPQ
    have e1 : Lam F ((i' : ℝ) + 1) ((T + k : ℕ) : ℝ) = Lam F (J : ℝ) (T : ℝ)
        + ((k : ℝ) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
      rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
      · linarith
      · push_cast; ring
    have e2 : Lam F (i' : ℝ) (((T + k : ℕ) : ℝ) + 1) = Lam F (J : ℝ) (T : ℝ)
        + (((k : ℝ) + 1) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
      rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
      · linarith
      · push_cast; ring
    have hseg : Lam F (J : ℝ) (T : ℝ) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) ∈
        segment ℝ (Lam F ((i' : ℝ) + 1) ((T + k : ℕ) : ℝ))
          (Lam F (i' : ℝ) (((T + k : ℕ) : ℝ) + 1)) := by
      rw [e1, e2, TraceCovering.segment_param]
      exact ⟨x, ⟨le_trans (min_le_left _ _) hkx, le_trans hxk.le (le_max_right _ _)⟩, rfl⟩
    have hmem : Lam F (J : ℝ) (T : ℝ) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)
        ∈ (D.tile iz).edge m := by
      rw [Tri.edge]
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hseg
      · rw [h1, h2, segment_symm]; exact hseg
    exact D.toDissection.edge_point_not_interior hmem i
  -- `X₀` is not straddled from below
  have hs : ¬ TraceCovering.Straddled D.toDissection (-(lev F)) (-(lev F F.A + ((J : ℝ) + T)))
      (Lam F (J : ℝ) (T : ℝ) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
    rw [zero_smul, add_zero]; exact hs0
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(lev F)) (-(lev F F.A + ((J : ℝ) + T)))
      (Lam F (J : ℝ) (T : ℝ) + ((J : ℝ) * ((e : ℝ) * f)) •
        ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
    refine TraceCovering.not_straddled_of_outside_after hgd hg hX hlev_ur hur0 (fun s hs => ?_)
    rw [hrow]
    apply Lam_neg F FC
    have : (J : ℝ) < s / ((e : ℝ) * f) := by rw [lt_div_iff₀ ha0]; exact hs
    linarith
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg hX hlev_ur hur1 hst hint hwall
    hs ht
  -- the given edge
  intro ε hε p q ℓ hℓ hp hpq hE
  have hpq' : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
    pts_ne _ (TraceCovering.fin3_succ_ne ε.2)
  have hPe : Lam F p q = Lam F (J : ℝ) (T : ℝ) +
      (((J : ℝ) - p) * ((e : ℝ) * f)) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
    rw [hrow, mul_div_cancel_right₀ _ ha0.ne']; congr 1
    · ring
    · linarith
  have hQe : Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f)) =
      Lam F (J : ℝ) (T : ℝ) + (((J : ℝ) - p) * ((e : ℝ) * f) + ℓ) •
        ((1 / ((e : ℝ) * f)) • vec F (-1) 1) := by
    rw [hrow, add_div, mul_div_cancel_right₀ _ ha0.ne']; congr 1
    · ring
    · linarith
  by_cases hin : ((J : ℝ) - p) * ((e : ℝ) * f) + ℓ ≤ (J : ℝ) * ((e : ℝ) * f)
  · have hx0 : 0 ≤ ((J : ℝ) - p) * ((e : ℝ) * f) := mul_nonneg (by linarith) ha0.le
    have hseg : ∀ x, 0 ≤ x → x ≤ (J : ℝ) * ((e : ℝ) * f) →
        Lam F (J : ℝ) (T : ℝ) + x • ((1 / ((e : ℝ) * f)) • vec F (-1) 1) ∈
          segment ℝ (Lam F (J : ℝ) (T : ℝ) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1))
            (Lam F (J : ℝ) (T : ℝ) + ((J : ℝ) * ((e : ℝ) * f)) •
              ((1 / ((e : ℝ) * f)) • vec F (-1) 1)) := by
      intro x hx0 hx1
      rw [TraceCovering.segment_param, min_eq_left hst, max_eq_right hst]
      exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
    have hb1 := hseg _ hx0 (by linarith)
    have hb2 := hseg _ (by linarith) hin
    rw [← hPe] at hb1
    rw [← hQe] at hb2
    have hsub : (D.tile ε.1).edge ε.2 ⊆ segment ℝ
        (Lam F (J : ℝ) (T : ℝ) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1))
        (Lam F (J : ℝ) (T : ℝ) + ((J : ℝ) * ((e : ℝ) * f)) •
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
    set sF := (D.toDissection.lineChain (-(lev F)) (-(lev F F.A + ((J : ℝ) + T)))).filter
      (fun ε' => (D.tile ε'.1).edge ε'.2 ⊆ segment ℝ
        (Lam F (J : ℝ) (T : ℝ) + (0 : ℝ) • ((1 / ((e : ℝ) * f)) • vec F (-1) 1))
        (Lam F (J : ℝ) (T : ℝ) + ((J : ℝ) * ((e : ℝ) * f)) •
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
          = ((J * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = J * (e * f) := by
        exact_mod_cast hreal
      have := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) J P' (Q' + 1) R'
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      omega
    · exfalso
      have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
          = ((J * (e * f) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = J * (e * f) := by
        exact_mod_cast hreal
      have hQ0 := Inflation.a_side_no_b e f (f ^ 2 - e ^ 2) J P' Q' (R' + 1)
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      rw [hQ0, zero_mul, add_zero] at hnat
      have := Inflation.a_side_rigid e f J P' (R' + 1) (by have := F.he; omega)
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
/-- **(B), one junction, general row end** (`row_one` with the row end and the two exclusions
abstracted): at `Y = Λ(i+1, t)` on row `J + T`, the tile across the up cell `Up i t`'s row flank
`vec(−1,1)` is the half-turn `Dn i t`, provided no straight tile passes through `Y` along the row
(`hedge`) and no other `γ`-tile has a flank along the row there (`hγ'`); the row word is `hall`
(`row_all_gen`). -/
theorem row_one_gen (L : LFrame F) (J T i t : ℕ) (hi : i + 1 ≤ J) (hit : i + 1 + t = J + T)
    (hf : J + T + 1 ≤ f)
    (hall : ∀ ε ∈ rowChain F ((J : ℝ) + T), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (J : ℝ) →
      p + q = (J : ℝ) + T →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    {iG : Fin N} (hrG : Set.range (D.tile iG).pts = Up F i t)
    (hedge : ∀ (z : Fin N) (m' : Fin 3),
      (D.tile z).basis.coord m' (Lam F ((i : ℝ) + 1) (t : ℝ)) = 0 →
      (∀ l, l ≠ m' → 0 < (D.tile z).basis.coord l (Lam F ((i : ℝ) + 1) (t : ℝ))) →
      cross ((D.tile z).pts (m' + 2) - (D.tile z).pts (m' + 1)) (vec F (-1) 1) = 0 → False)
    (hγz : ∀ (z : Fin N), z ≠ iG → ∀ (mz : Fin 3) (U W : Plane) (S : ℝ),
      (D.tile z).pts mz = Lam F ((i : ℝ) + 1) (t : ℝ) →
      IsFlankPair (D.tile z) mz (Lam F ((i : ℝ) + 1) (t : ℝ)) U W → 0 < S →
      vec F (-1) 1 = S • U → (D.tile z).localAngle (Lam F ((i : ℝ) + 1) (t : ℝ)) ≠ γ) :
    Present D (Dn F i t) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hK := K_ne F FC
  have hK2 := mul_self_pos.mpr hK
  have hitR : (i : ℝ) + 1 + t = J + T := by exact_mod_cast hit
  have hR : (J : ℝ) + T + 1 ≤ f := by exact_mod_cast hf
  have hij : (i : ℝ) + 1 ≤ J := by exact_mod_cast hi
  have hYint : Lam F ((i : ℝ) + 1) (t : ℝ) ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) (by positivity) (by linarith)
  have rG : Set.range (D.tile iG).pts = {Lam F ((i : ℝ) + 1) (t : ℝ),
      Lam F i ((t : ℝ) + 1), Lam F i t} := by
    rw [hrG]; simp only [Up]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨mG, hmG, hflG⟩ := flank_of_range rG
  rw [Lam_sub_eq F (by ring : (i : ℝ) - ((i : ℝ) + 1) = -1)
      (by ring : ((t : ℝ) + 1) - (t : ℝ) = 1),
    Lam_sub_eq F (by ring : (i : ℝ) - ((i : ℝ) + 1) = -1)
      (by ring : (t : ℝ) - (t : ℝ) = 0)] at hflG
  obtain ⟨z, hzG, hYz, hcz⟩ := flank_neighbour_dissection D.toDissection hYint hmG hflG
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', hm0, hmpos, hcr, -⟩
  swap
  · exact (hedge z m' hm0 hmpos hcr).elim
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
  have hY : lev F (Lam F ((i : ℝ) + 1) (t : ℝ)) = lev F F.A + ((J : ℝ) + T) := by
    rw [lev_Lam F FC]; linarith
  have hall3 : ∀ k, lev F F.A + ((J : ℝ) + T) ≤ lev F ((D.tile z).pts k) := by
    intro k
    have hk : (D.tile z).pts k ∈ Set.range (D.tile z).pts := ⟨k, rfl⟩
    rw [ApexPlacement.range_of_flank hmz hUW] at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h <;> rw [h]
    · rw [hY]
    · rw [map_add, hY, hlevU, add_zero]
    · rw [map_add, hY]; linarith
  -- the row edge `[Y, Y + U]` is a lower-side edge of the row
  obtain ⟨idx, hidx, hE⟩ : ∃ idx : Fin 3, (z, idx) ∈ rowChain F ((J : ℝ) + T) ∧
      EdgeIs D (z, idx) (Lam F ((i : ℝ) + 1) (t : ℝ))
        (Lam F ((i : ℝ) + 1) (t : ℝ) + U) := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · have e1 : (D.tile z).pts (mz + 1) = Lam F ((i : ℝ) + 1) (t : ℝ) + U := by
        rw [h1]; abel
      refine ⟨mz, mem_rowChain F (by rw [hmz, hY]) (by rw [e1, map_add, hY, hlevU, add_zero])
        hall3, ?_⟩
      simp only [EdgeIs]; rw [hmz, e1]
    · have e1 : (D.tile z).pts (mz + 2) = Lam F ((i : ℝ) + 1) (t : ℝ) + U := by
        rw [h1]; abel
      have e2 : (D.tile z).pts (mz + 2 + 1) = Lam F ((i : ℝ) + 1) (t : ℝ) := by
        rw [fin3_add_two_add_one]; exact hmz
      refine ⟨mz + 2, mem_rowChain F (by rw [e1, map_add, hY, hlevU, add_zero])
        (by rw [e2, hY]) hall3, ?_⟩
      simp only [EdgeIs]; rw [e1, e2, Set.pair_comm]
  have hUlam : Lam F ((i : ℝ) + 1) (t : ℝ) + U = Lam F ((i : ℝ) + 1 - ℓ / ((e : ℝ) * f))
      ((t : ℝ) + ℓ / ((e : ℝ) * f)) := by
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
    simp only [Dn]
  · exact absurd hz (hγz z hzG mz U W S hmz hUW hS hU0)


/-! ## §2 `V` in lattice coordinates: `V − A = vec (1 + c/b) (−1)` (the reflection of `v` in `m₀`) -/

/-- `c/b`. -/
noncomputable def cb (e f : ℕ) : ℝ := (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)

include F in
theorem cb_pos : 0 < cb e f ∧ 1 < cb e f := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  exact ⟨div_pos hc0 hb0, by rw [cb, lt_div_iff₀ hb0, one_mul]; exact hbc⟩

theorem norm_V : ‖vec F (1 + cb e f) (-1)‖ = (f : ℝ) ^ 2 := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  apply norm_of_sq hc0.le _ (norm_nonneg _)
  rw [norm_vec_sq, cb]
  field_simp
  ring

theorem norm_VP : ‖vec F (cb e f) (-1)‖ = (e : ℝ) * f := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  apply norm_of_sq ha0.le _ (norm_nonneg _)
  rw [norm_vec_sq, cb]
  field_simp
  ring

theorem norm_MN : ‖vec F (cb e f) (-1 - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)‖ = (f : ℝ) ^ 2 := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
  apply norm_of_sq hc0.le _ (norm_nonneg _)
  rw [norm_vec_sq, cb]
  field_simp
  ring

theorem P_eq : F.P = Lam F 1 0 := by simp [Lam, vec, w]

/-- **`V` in lattice coordinates.**  `T₂ = (A, V, P′)` and `T₃ = (A, P′, J₁)` share the `b`-edge
`AP′` with equal distances to the third vertex (`c` from `A`, `a` from `P′`) and lie on opposite
sides of `m₀` (cone coordinates: `s₃ > t₃`), so `V` is the reflection of `J₁ = A + v` in `m₀`
(`third_vertex_cross`). -/
theorem V_eq (FC : ApexPlacement.FrameCoords F) : F.V = Lam F (1 + cb e f) (-1) := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hf : (0 : ℝ) < f := f_pos' F
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  obtain ⟨s3, t3, hs3, ht3, hP, hv3, hsum3⟩ := FC.hP
  obtain ⟨s1, t1, hs1, ht1, hV1, hv1, hsum1⟩ := FC.hV
  have hK3 : 0 < 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have es1 : s1 = t3 := by
    have : s1 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = t3 * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      rw [hv1, hv3]
    exact mul_right_cancel₀ hK3.ne' this
  have et1 : t1 = s3 := by linarith
  have h2t : 0 < 1 - 2 * t3 * f := by
    have : (1 - 2 * t3 * f) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      linear_combination (-2 * (f : ℝ)) * hv3
    exact pos_of_mul_pos_left (this ▸ hb0) hK3.le
  have hf0 : (f : ℝ) ≠ 0 := hf.ne'
  have hst : t3 < s3 := by
    have hs3' : s3 = 1 / f - t3 := by linarith
    have : s3 - t3 = (1 - 2 * t3 * f) / f := by rw [hs3']; field_simp; ring
    have : 0 < s3 - t3 := by rw [this]; positivity
    linarith
  set Q : Plane := ((f : ℝ) ^ 3) • F.uL with hQ
  set R' : Plane := F.R - F.A with hR'
  have hX : cross Q R' ≠ 0 := by
    have := FC.hcone.det
    rwa [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = Q by rw [hQ]; abel] at this
  have huL : F.uL = (1 / (f : ℝ) ^ 3) • Q := by
    rw [hQ, smul_smul, one_div_mul_cancel (by positivity), one_smul]
  have hVA : F.V - F.A = ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • (s1 • Q + t1 • R') := by
    rw [F.hV, add_sub_cancel_left, ← hV1, smul_smul, div_mul_cancel₀ _ hb0.ne']
  have hwA : F.P - F.A = s3 • Q + t3 • R' := hP
  apply third_vertex_cross (X := F.A) (Y := F.P)
  · intro h; have := F.hAP; rw [h, dist_self] at this; linarith
  · have e1 : cross (F.P - F.A) (F.V - F.A) = (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((s3 * s3 - t3 * t3) * cross Q R') := by
      rw [hwA, hVA, es1, et1]
      simp only [cross_add_left', cross_add_right, cross_smul_left', cross_smul_right, cross_self']
      rw [cross_anti Q R']; ring
    have e2 : cross (F.P - F.A) (Lam F (1 + cb e f) (-1) - F.A) = t3 / (f : ℝ) * cross Q R' := by
      have : Lam F (1 + cb e f) (-1) - F.A = vec F (1 + cb e f) (-1) := by
        simp only [Lam]; abel
      rw [this, show F.P - F.A = vec F 1 0 by simp [vec, w], cross_vec]
      rw [show w F = s3 • Q + t3 • R' from hwA, huL]
      simp only [cross_add_left', cross_smul_left', cross_smul_right, cross_self']
      rw [cross_anti Q R']
      field_simp
      ring
    rw [e1, e2]
    have hs : 0 < s3 * s3 - t3 * t3 := by nlinarith
    have : 0 < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((s3 * s3 - t3 * t3) * cross Q R') *
        (t3 / (f : ℝ) * cross Q R') ↔ 0 < (f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
          (s3 * s3 - t3 * t3) * (t3 / (f : ℝ)) * (cross Q R' * cross Q R') := by
      constructor <;> intro h <;> linarith [h]
    rw [this]
    have := mul_self_pos.mpr hX
    positivity
  · rw [F.hV, HalfTurnR3R4Glue.dist_self_add_unit F.huR hc0.le, dist_eq_norm,
      show F.A - Lam F (1 + cb e f) (-1) = -vec F (1 + cb e f) (-1) by simp only [Lam]; abel,
      norm_neg, norm_V]
  · rw [dist_comm, F.hVP, dist_eq_norm, P_eq F, Lam_sub, show (1 : ℝ) - (1 + cb e f) = -cb e f by
      ring, show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-cb e f) 1 = - vec F (cb e f) (-1) by rw [vec_neg]; norm_num, norm_neg, norm_VP]

/-! ## §3 The column, the level mirror, in lattice coordinates -/

/-- `T₂ + jP′` (the column on the matched ray `m₀`, translate of `T₂ = (A, V, P′)` by `j·(P′ − A)`). -/
def Col (F : HFrame D e f α β γ) (j : ℕ) : Set Plane :=
  {F.A + (j : ℝ) • (F.P - F.A), F.V + (j : ℝ) • (F.P - F.A), F.P + (j : ℝ) • (F.P - F.A)}

/-- `N_q = M₁ + (q−1)P′`, `M₁ = {V, P′, P′ + b·uL}` the mirror of `T₂` across its `a`-edge `VP′`
(the (M)-tile of R2, `MirrorStripR2Glue.R2Frame.hMir`). -/
def Nq (F : HFrame D e f α β γ) (q : ℕ) : Set Plane :=
  {F.V + ((q : ℝ) - 1) • (F.P - F.A), F.P + ((q : ℝ) - 1) • (F.P - F.A),
    F.P + ((q : ℝ) - 1) • (F.P - F.A) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL}

theorem Col_eq (FC : ApexPlacement.FrameCoords F) (j : ℕ) :
    Col F j = {Lam F j 0, Lam F ((j : ℝ) + 1 + cb e f) (-1), Lam F ((j : ℝ) + 1) 0} := by
  have e1 : F.A + (j : ℝ) • (F.P - F.A) = Lam F j 0 := by simp [Lam, vec, w]
  have e2 : F.V + (j : ℝ) • (F.P - F.A) = Lam F ((j : ℝ) + 1 + cb e f) (-1) := by
    rw [V_eq F FC]; simp only [Lam, vec, w]; module
  have e3 : F.P + (j : ℝ) • (F.P - F.A) = Lam F ((j : ℝ) + 1) 0 := by
    simp only [Lam, vec, w]; module
  rw [Col, e1, e2, e3]

theorem Nq_eq (FC : ApexPlacement.FrameCoords F) (q : ℕ) :
    Nq F q = {Lam F ((q : ℝ) + cb e f) (-1), Lam F q 0,
      Lam F q (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)} := by
  obtain ⟨-, -, hc0, -, -⟩ := consts F
  have hb : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL
      = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) • v F := by
    rw [v, smul_smul, div_mul_cancel₀ _ hc0.ne']
  have e1 : F.V + ((q : ℝ) - 1) • (F.P - F.A) = Lam F ((q : ℝ) + cb e f) (-1) := by
    rw [V_eq F FC]; simp only [Lam, vec, w]; module
  have e2 : F.P + ((q : ℝ) - 1) • (F.P - F.A) = Lam F q 0 := by
    simp only [Lam, vec, w]; module
  have e3 : Lam F q 0 + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uL
      = Lam F q (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) := by
    rw [hb]; simp only [Lam, vec, w]; module
  rw [Nq, e1, e2, e3]

theorem vec_add (p q r s : ℝ) : vec F p q + vec F r s = vec F (p + r) (q + s) := by
  simp only [vec]; module

/-! ## §4 Counting at a point -/

include F in
/-- With an `α` and two distinct `γ`'s at an interior point: no straight tile, and at most two `γ`'s. -/
theorem count_ag {x : Plane} (hx : x ∈ interior D.target.carrier) {iA iG1 iG2 : Fin N}
    (h12 : iG1 ≠ iG2) (gA : (D.tile iA).localAngle x = α) (g1 : (D.tile iG1).localAngle x = γ)
    (g2 : (D.tile iG2).localAngle x = γ) :
    (∀ z, (D.tile z).localAngle x ≠ Real.pi ∧ (D.tile z).localAngle x ≠ 2 * Real.pi) ∧
      ({i | (D.tile i).localAngle x = γ} : Finset (Fin N)).card ≤ 2 := by
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hx
  have cA := card_one gA
  have cG := card_two h12 g1 g2
  refine ⟨fun z => ⟨fun h => ?_, fun h => ?_⟩, by omega⟩
  · have := card_one h; omega
  · have := card_one h; omega

include F in
/-- With three distinct `γ`'s at an interior point: no straight tile, exactly three `γ`'s. -/
theorem count_ggg {x : Plane} (hx : x ∈ interior D.target.carrier) {i1 i2 i3 : Fin N}
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) (g1 : (D.tile i1).localAngle x = γ)
    (g2 : (D.tile i2).localAngle x = γ) (g3 : (D.tile i3).localAngle x = γ) :
    (∀ z, (D.tile z).localAngle x ≠ Real.pi ∧ (D.tile z).localAngle x ≠ 2 * Real.pi) ∧
      ∀ z, (D.tile z).localAngle x = γ → z = i1 ∨ z = i2 ∨ z = i3 := by
  classical
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hx
  have hsub : ({i1, i2, i3} : Finset (Fin N)) ⊆
      ({i | (D.tile i).localAngle x = γ} : Finset (Fin N)) := by
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_filter_of g1
    · exact mem_filter_of g2
    · exact mem_filter_of g3
  have h3 : ({i1, i2, i3} : Finset (Fin N)).card = 3 :=
    Finset.card_eq_three.mpr ⟨i1, i2, i3, h12, h13, h23, rfl⟩
  have cG := Finset.card_le_card hsub
  rw [h3] at cG
  refine ⟨fun z => ⟨fun h => ?_, fun h => ?_⟩, fun z hz => ?_⟩
  · have := card_one h; omega
  · have := card_one h; omega
  · have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h3]; omega)
    have : z ∈ ({i1, i2, i3} : Finset (Fin N)) := by rw [heq]; exact mem_filter_of hz
    simpa using this

/-- No straight tile at `Y`: the edge case of `flank_neighbour` cannot occur. -/
theorem hedge_of_ns {Y : Plane} (hns : ∀ z, (D.tile z).localAngle Y ≠ Real.pi ∧
      (D.tile z).localAngle Y ≠ 2 * Real.pi) (U : Plane) :
    ∀ (z : Fin N) (m' : Fin 3), (D.tile z).basis.coord m' Y = 0 →
      (∀ l, l ≠ m' → 0 < (D.tile z).basis.coord l Y) →
      cross ((D.tile z).pts (m' + 2) - (D.tile z).pts (m' + 1)) U = 0 → False := by
  intro z m' hm0 hmpos _
  have hYz : Y ∈ (D.tile z).carrier := by
    rw [NearBaseVertex.mem_carrier_iff]; intro l
    by_cases hl : l = m'
    · rw [hl, hm0]
    · exact (hmpos l hl).le
  have hznv : ∀ q, (D.tile z).pts q ≠ Y := fun q hq =>
    NearBaseVertex.vertex_not_edge _ q hq m' hmpos
  rcases localAngle_mem_pi_of_mem (D.tile z) hYz hznv with h | h
  · exact (hns z).2 h
  · exact (hns z).1 h

/-- No straight tile at `Y`: `Y` is not straddled from any side of any line. -/
theorem nstr_of_ns {Y : Plane} (hns : ∀ z, (D.tile z).localAngle Y ≠ Real.pi ∧
      (D.tile z).localAngle Y ≠ 2 * Real.pi) (g : Plane →ₗ[ℝ] ℝ) (d : ℝ) :
    ¬ TraceCovering.Straddled D.toDissection g d Y := by
  rintro ⟨ε, -, hx⟩
  rcases straight_count hx with h | h
  · exact (hns _).2 h
  · exact (hns _).1 h

/-! ## §5 (1) The matched ray is `b^q` -/

/-- The left (`Λ₃`) side of the matched ray `m₀ = {rho = rho A}`: edges on `m₀` whose tile lies in
`{rho ≥ rho A}`. -/
noncomputable def leftChain (F : HFrame D e f α β γ) : Finset (Fin N × Fin 3) :=
  D.toDissection.lineChain (-(rho F)) (-(rho F F.A))

theorem rho_Lam (FC : ApexPlacement.FrameCoords F) (x y : ℝ) :
    rho F (Lam F x y) = rho F F.A + y := by
  rw [Lam, map_add, rho_vec F FC]

theorem rho_ne (FC : ApexPlacement.FrameCoords F) : rho F ≠ 0 := by
  intro h; have := rho_vec F FC 0 1; rw [h, LinearMap.zero_apply] at this; exact zero_ne_one this

/-- **(1) The matched ray.**  Given the column `T₂ + jP′` (`j < q`) and `N_q`: `[A, qP′]` is a wall
(right side: the column's `b`-edges), `A` and `qP′` are not straddled from the left (`N_q`'s
interior reaches `m₀` just past `qP′`: `w = (b/c)·(V − P′) + b·uL` lies in its `γ`-corner), so the
left side is a whole-edge word of value `q·b`, which is `b^q` by **m = 1** (`Inflation.b_side_rigid`,
`q < f`; at N = 44, `3b = a + c`).  Stated for a left edge leaving `Λ(x, 0)`, `x < q`, down `m₀`. -/
theorem matched_word (L : LFrame F) (q : ℕ) (hq1 : 1 ≤ q) (hqf : q + 1 ≤ f)
    (hcol : ∀ j < q, Present D (Col F j)) (hN : Present D (Nq F q)) :
    ∀ ε ∈ leftChain F, ∀ x ℓ : ℝ, 0 ≤ x → x < q → 0 < ℓ →
      EdgeIs D ε (Lam F x 0) (Lam F (x + ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0) →
      ℓ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  have hqR : (q : ℝ) + 1 ≤ f := by exact_mod_cast hqf
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hu1 : ‖(1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0‖ = 1 := by
    rw [norm_smul, norm_vec_10, Real.norm_of_nonneg (by positivity), one_div_mul_cancel hb0.ne']
  have hu0 := TraceCovering.ne_zero_of_norm hu1
  have hrho_u : rho F ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) = 0 := by
    rw [map_smul, rho_vec F FC, smul_zero]
  have hg : rho F ≠ 0 := rho_ne F FC
  have hg' : (-(rho F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(rho F)) y = -(rho F F.A) ↔ rho F y = rho F F.A := TraceCovering.neg_iff
  have hX : rho F (Lam F 0 0) = rho F F.A := by rw [rho_Lam F FC, add_zero]
  have hrow : ∀ x : ℝ, Lam F 0 0 + x • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)
      = Lam F (x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0 := by
    intro x; rw [smul_smul, vec_smul]; apply Lam_add_eq F <;> ring
  have hst : (0 : ℝ) ≤ (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by positivity
  have hint : ∀ x ∈ Set.Ioo 0 ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)),
      Lam F 0 0 + x • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) ∈ interior D.target.carrier := by
    intro x hx
    rw [hrow]
    have h1 : x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < q := by rw [div_lt_iff₀ hb0]; exact hx.2
    exact Lam_interior F FC (div_pos hx.1 hb0) le_rfl (by linarith)
  have hwall : ∀ x ∈ Set.Ioo 0 ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)), ∀ i,
      Lam F 0 0 + x • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)
        ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hq0 : 0 ≤ x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := div_nonneg hx.1.le hb0.le
    have hk1 : ((⌊x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)⌋₊ : ℕ) : ℝ) ≤ x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
      Nat.floor_le hq0
    have hk2 : x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((⌊x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    set k := ⌊x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)⌋₊ with hk
    have hkx : (k : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≤ x := by rwa [le_div_iff₀ hb0] at hk1
    have hxk : x < ((k : ℝ) + 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rwa [div_lt_iff₀ hb0] at hk2
    have hkq : k < q := by
      have h1 : (k : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
        lt_of_le_of_lt hkx hx.2
      exact_mod_cast lt_of_mul_lt_mul_right h1 hb0.le
    obtain ⟨iz, hiz⟩ := hcol k hkq
    rw [Col_eq F FC] at hiz
    have hP : Lam F k 0 ∈ Set.range (D.tile iz).pts := by rw [hiz]; exact mem3_1
    have hQ : Lam F ((k : ℝ) + 1) 0 ∈ Set.range (D.tile iz).pts := by rw [hiz]; exact mem3_3
    obtain ⟨m, hm⟩ := edge_idx hP hQ (Lam_ne F FC (Or.inl (by intro h; linarith)))
    have e1 : Lam F k 0 = Lam F 0 0 + ((k : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
        ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) := by
      rw [hrow, mul_div_cancel_right₀ _ hb0.ne']
    have e2 : Lam F ((k : ℝ) + 1) 0 = Lam F 0 0 + (((k : ℝ) + 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
        ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) := by
      rw [hrow, mul_div_cancel_right₀ _ hb0.ne']
    have hseg : Lam F 0 0 + x • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) ∈
        segment ℝ (Lam F k 0) (Lam F ((k : ℝ) + 1) 0) := by
      rw [e1, e2, TraceCovering.segment_param]
      exact ⟨x, ⟨le_trans (min_le_left _ _) hkx, le_trans hxk.le (le_max_right _ _)⟩, rfl⟩
    have hmem : Lam F 0 0 + x • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)
        ∈ (D.tile iz).edge m := by
      rw [Tri.edge]
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hseg
      · rw [h1, h2, segment_symm]; exact hseg
    exact D.toDissection.edge_point_not_interior hmem i
  have hs : ¬ TraceCovering.Straddled D.toDissection (-(rho F)) (-(rho F F.A))
      (Lam F 0 0 + (0 : ℝ) • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)) := by
    refine TraceCovering.not_straddled_of_outside_before hgd hg hX hrho_u hu0 (fun t ht => ?_)
    rw [hrow]; exact Lam_neg F FC (div_neg_of_neg_of_pos ht hb0) 0
  -- `qP′` is not straddled from the left: `N_q`'s interior reaches `m₀` just past it
  have ht : ¬ TraceCovering.Straddled D.toDissection (-(rho F)) (-(rho F F.A))
      (Lam F 0 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
        ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)) := by
    refine TraceCovering.not_straddled_of_near_interior hgd hg hX hrho_u hu0 (fun δ hδ => ?_)
    obtain ⟨iN, hrN⟩ := hN
    rw [Nq_eq F FC] at hrN
    have rN : Set.range (D.tile iN).pts = {Lam F q 0, Lam F ((q : ℝ) + cb e f) (-1),
        Lam F q (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)} := by
      rw [hrN]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    obtain ⟨mN, hmN, hflN⟩ := flank_of_range rN
    rw [Lam_sub_eq F (by ring : ((q : ℝ) + cb e f) - q = cb e f) (by ring : (-1 : ℝ) - 0 = -1),
      Lam_sub_eq F (by ring : (q : ℝ) - q = 0)
        (by ring : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 - 0 =
          ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)] at hflN
    have hσ : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
    set ε' : ℝ := min (δ / (2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      (1 / (2 * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1))) with hε'
    have hε0 : 0 < ε' := lt_min (by positivity) (by positivity)
    have hε1 : ε' * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1) < 1 := by
      have h := min_le_right (δ / (2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        (1 / (2 * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1)))
      rw [← hε'] at h
      have hp : 0 < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1 := by positivity
      calc ε' * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1)
          ≤ 1 / (2 * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1)) *
            (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1) := mul_le_mul_of_nonneg_right h hp.le
        _ = 1 / 2 := by field_simp
        _ < 1 := by norm_num
    have hεδ : ε' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < δ := by
      have h := min_le_left (δ / (2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
        (1 / (2 * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 + 1)))
      rw [← hε'] at h
      calc ε' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ≤ δ / (2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) *
            ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h hb0.le
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    refine ⟨(q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + ε' * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2), ?_, iN, ?_⟩
    · rw [add_sub_cancel_left, abs_of_pos (by positivity)]; exact hεδ
    have hin := open_dir_interior (D.tile iN) mN hmN hflN hσ one_pos hε0 hε1
    have hcomb : (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) • vec F (cb e f) (-1)
        + (1 : ℝ) • vec F 0 (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) = vec F 1 0 := by
      have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
      rw [vec_smul, one_smul, vec_add, cb]
      congr 1
      · field_simp; ring
      · ring
    rw [hcomb, vec_smul, mul_one, mul_zero, Lam_add, add_zero] at hin
    rw [hrow]
    convert hin using 2
    field_simp
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg hX hrho_u hu1 hst hint hwall
    hs ht
  -- the given edge
  intro ε hε x ℓ hx0 hxq hℓ hE
  have hpq' : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
    pts_ne _ (TraceCovering.fin3_succ_ne ε.2)
  have hPe : Lam F x 0 = Lam F 0 0 + (x * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
      ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) := by
    rw [hrow, mul_div_cancel_right₀ _ hb0.ne']
  have hQe : Lam F (x + ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0 = Lam F 0 0 +
      (x * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + ℓ) • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) := by
    rw [hrow, add_div, mul_div_cancel_right₀ _ hb0.ne']
  by_cases hin : x * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + ℓ ≤ (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
  · have hx0' : 0 ≤ x * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := mul_nonneg hx0 hb0.le
    have hseg : ∀ y, 0 ≤ y → y ≤ (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
        Lam F 0 0 + y • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) ∈
          segment ℝ (Lam F 0 0 + (0 : ℝ) • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0))
            (Lam F 0 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
              ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)) := by
      intro y hy0 hy1
      rw [TraceCovering.segment_param, min_eq_left hst, max_eq_right hst]
      exact ⟨y, ⟨hy0, hy1⟩, rfl⟩
    have hb1 := hseg _ hx0' (by linarith)
    have hb2 := hseg _ (by linarith) hin
    rw [← hPe] at hb1
    rw [← hQe] at hb2
    have hsub : (D.tile ε.1).edge ε.2 ⊆ segment ℝ
        (Lam F 0 0 + (0 : ℝ) • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0))
        (Lam F 0 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
          ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0)) := by
      rw [Tri.edge]
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact (convex_segment _ _).segment_subset hb1 hb2
      · exact (convex_segment _ _).segment_subset hb2 hb1
    have hd : dist (Lam F x 0) (Lam F (x + ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0) = ℓ := by
      rw [hPe, hQe, TraceCovering.dist_param hu1, max_eq_right (by linarith),
        min_eq_left (by linarith)]; ring
    have hdM : dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = ℓ := by
      rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hd
      · rw [h1, h2, dist_comm]; exact hd
    set sF := (D.toDissection.lineChain (-(rho F)) (-(rho F F.A))).filter
      (fun ε' => (D.tile ε'.1).edge ε'.2 ⊆ segment ℝ
        (Lam F 0 0 + (0 : ℝ) • ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0))
        (Lam F 0 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
          ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0))) with hsF
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
    · exfalso
      have hreal : (((P' + 1) * (e * f) + Q' * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
          = ((q * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : (P' + 1) * (e * f) + Q' * (f ^ 2 - e ^ 2) + R' * f ^ 2 = q * (f ^ 2 - e ^ 2) := by
        exact_mod_cast hreal
      have := Inflation.b_side_rigid e f (f ^ 2 - e ^ 2) q (P' + 1) Q' R'
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      omega
    · exact h
    · exfalso
      have hreal : ((P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 : ℕ) : ℝ)
          = ((q * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub hee]; rw [h] at hsum; linarith
      have hnat : P' * (e * f) + Q' * (f ^ 2 - e ^ 2) + (R' + 1) * f ^ 2 = q * (f ^ 2 - e ^ 2) := by
        exact_mod_cast hreal
      have := Inflation.b_side_rigid e f (f ^ 2 - e ^ 2) q P' Q' (R' + 1)
        (by have := F.he; omega) (by have := F.hef; omega) F.hco hb' (by omega) hnat
      omega
  · -- the edge would straddle `qP′` from the left
    exfalso
    push Not at hin
    apply ht
    refine ⟨ε, hε, ?_⟩
    have hxq' : x * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < (q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
      mul_lt_mul_of_pos_right hxq hb0
    have hopen : Lam F 0 0 + ((q : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
        ((1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0) ∈
        openSegment ℝ (Lam F x 0) (Lam F (x + ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0) := by
      rw [hPe, hQe, TraceCovering.openSegment_param (by linarith), min_eq_left (by linarith),
        max_eq_right (by linarith)]
      exact ⟨_, ⟨hxq', hin⟩, rfl⟩
    rcases pair_cases hE hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hopen
    · rw [openSegment_symm]; exact hopen

theorem mem_leftChain {z : Fin N} {m : Fin 3}
    (h1 : rho F ((D.tile z).pts m) = rho F F.A) (h2 : rho F ((D.tile z).pts (m + 1)) = rho F F.A)
    (hall : ∀ k, rho F F.A ≤ rho F ((D.tile z).pts k)) : (z, m) ∈ leftChain F := by
  rw [leftChain, Dissection.mem_lineChain]
  simp only [LinearMap.neg_apply, neg_inj, neg_le_neg_iff]
  exact ⟨h1, h2, hall⟩

/-! ## §6 (2) The slot at `nP′` on the matched ray -/

set_option maxHeartbeats 1000000 in
/-- **The matched slot `(n+1)P′`** (`n + 1 < q`).  Around `X = Λ(n+1, 0)`: the column tiles
`T₂ + (n+1)P′` (`α`) and `T₂ + nP′` (`γ`), and `T₃ + nP′ = Up n 0` (`γ`); no straight tile fits
(`count_ag`).  The tile across `T₂ + (n+1)P′`'s flank `w` lies on the `Λ₃` side of `m₀` with an edge on
`m₀` from `X`, which is a `b`-edge (`matched_word`), so it is not `β`, not one of the two `γ`'s, and
is the `α`-tile `T₃ + (n+1)P′ = Up (n+1) 0`. -/
theorem matched_slot (L : LFrame F) (q n : ℕ) (hnq : n + 2 ≤ q) (hqf : q + 1 ≤ f)
    (hword : ∀ ε ∈ leftChain F, ∀ x ℓ : ℝ, 0 ≤ x → x < q → 0 < ℓ →
      EdgeIs D ε (Lam F x 0) (Lam F (x + ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0) →
      ℓ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hc1 : Present D (Col F (n + 1))) (hc0 : Present D (Col F n)) (hU : Present D (Up F n 0)) :
    Present D (Up F (n + 1) 0) := by
  classical
  have FC := L.FC
  obtain ⟨ha0, hb0, hc0', hbc, hac⟩ := consts F
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hK := K_ne F FC
  have hK2 := mul_self_pos.mpr hK
  have hnR : (n : ℝ) + 2 ≤ q := by exact_mod_cast hnq
  have hqR : (q : ℝ) + 1 ≤ f := by exact_mod_cast hqf
  have hXint : Lam F ((n : ℝ) + 1) 0 ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) le_rfl (by linarith)
  obtain ⟨i1, hr1⟩ := hc1
  obtain ⟨i0, hr0⟩ := hc0
  obtain ⟨iU, hrU⟩ := hU
  rw [Col_eq F FC] at hr1 hr0
  push_cast at hr1
  have r1 : Set.range (D.tile i1).pts = {Lam F ((n : ℝ) + 1) 0, Lam F ((n : ℝ) + 1 + 1) 0,
      Lam F ((n : ℝ) + 1 + 1 + cb e f) (-1)} := by
    rw [hr1]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have r0 : Set.range (D.tile i0).pts = {Lam F ((n : ℝ) + 1) 0, Lam F n 0,
      Lam F ((n : ℝ) + 1 + cb e f) (-1)} := by
    rw [hr0]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rU : Set.range (D.tile iU).pts = {Lam F ((n : ℝ) + 1) 0, Lam F n 0, Lam F n 1} := by
    rw [hrU]; simp only [Up, Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have g1 : (D.tile i1).localAngle (Lam F ((n : ℝ) + 1) 0) = α := by
    apply (angle_of_range F r1).1
    rw [dist_Lam, show (n : ℝ) + 1 + 1 - ((n : ℝ) + 1 + 1 + cb e f) = -cb e f by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-cb e f) 1 = - vec F (cb e f) (-1) by rw [vec_neg]; norm_num, norm_neg, norm_VP]
  have g0 : (D.tile i0).localAngle (Lam F ((n : ℝ) + 1) 0) = γ := by
    apply (angle_of_range F r0).2.2
    rw [dist_Lam, show (n : ℝ) - ((n : ℝ) + 1 + cb e f) = -(1 + cb e f) by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  have gU : (D.tile iU).localAngle (Lam F ((n : ℝ) + 1) 0) = γ := by
    have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have h0U : i0 ≠ iU := (ne_of_range rU r0 (p := Lam F n 1) mem3_3
    (not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)))).symm
  obtain ⟨hns, cG⟩ := count_ag F hXint h0U g1 g0 gU
  obtain ⟨m1, hm1, hfl1⟩ := flank_of_range r1
  rw [Lam_sub_eq F (by ring : ((n : ℝ) + 1 + 1) - ((n : ℝ) + 1) = 1) (by ring : (0 : ℝ) - 0 = 0),
    Lam_sub_eq F (by ring : ((n : ℝ) + 1 + 1 + cb e f) - ((n : ℝ) + 1) = 1 + cb e f)
      (by ring : (-1 : ℝ) - 0 = -1)] at hfl1
  obtain ⟨z, hz1, hXz, hcz⟩ := flank_neighbour_dissection D.toDissection hXint hm1 hfl1
  rcases hcz with ⟨mz, hmz, U, W, hUW, S, hS, hU0, hside⟩ | ⟨m', hm0, hmpos, hcr, -⟩
  swap
  · exact (hedge_of_ns hns (vec F 1 0) z m' hm0 hmpos hcr).elim
  have hU0n : ‖vec F 1 0‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := norm_vec_10 F
  have hUne : U ≠ 0 := by
    intro h; rw [h, smul_zero] at hU0; rw [hU0, norm_zero] at hU0n; linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ‖U‖ = ℓ := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := hℓdef ▸ norm_pos_iff.mpr hUne
  have hUe : U = (ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • vec F 1 0 := flank_eq hS hU0 hℓdef hU0n hb0
  have hrhoU : rho F U = 0 := by
    have := congrArg (rho F) hU0
    rw [map_smul, rho_vec F FC, smul_eq_mul] at this
    rcases mul_eq_zero.mp (by linarith : S * rho F U = 0) with h | h
    · linarith
    · exact h
  have hrhoW : 0 < rho F W := by
    have hW := vec_coords F FC W
    rw [hW, cross_vec, cross_vec] at hside
    rw [hW, rho_vec F FC]
    nlinarith
  have hY : rho F (Lam F ((n : ℝ) + 1) 0) = rho F F.A := by rw [rho_Lam F FC, add_zero]
  have hall3 : ∀ k, rho F F.A ≤ rho F ((D.tile z).pts k) := by
    intro k
    have hk : (D.tile z).pts k ∈ Set.range (D.tile z).pts := ⟨k, rfl⟩
    rw [ApexPlacement.range_of_flank hmz hUW] at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h | h | h <;> rw [h]
    · rw [hY]
    · rw [map_add, hY, hrhoU, add_zero]
    · rw [map_add, hY]; linarith
  obtain ⟨idx, hidx, hE⟩ : ∃ idx : Fin 3, (z, idx) ∈ leftChain F ∧
      EdgeIs D (z, idx) (Lam F ((n : ℝ) + 1) 0) (Lam F ((n : ℝ) + 1) 0 + U) := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · have e1 : (D.tile z).pts (mz + 1) = Lam F ((n : ℝ) + 1) 0 + U := by rw [h1]; abel
      refine ⟨mz, mem_leftChain F (by rw [hmz, hY]) (by rw [e1, map_add, hY, hrhoU, add_zero])
        hall3, ?_⟩
      simp only [EdgeIs]; rw [hmz, e1]
    · have e1 : (D.tile z).pts (mz + 2) = Lam F ((n : ℝ) + 1) 0 + U := by rw [h1]; abel
      have e2 : (D.tile z).pts (mz + 2 + 1) = Lam F ((n : ℝ) + 1) 0 := by
        rw [fin3_add_two_add_one]; exact hmz
      refine ⟨mz + 2, mem_leftChain F (by rw [e1, map_add, hY, hrhoU, add_zero])
        (by rw [e2, hY]) hall3, ?_⟩
      simp only [EdgeIs]; rw [e1, e2, Set.pair_comm]
  have hUlam : Lam F ((n : ℝ) + 1) 0 + U =
      Lam F ((n : ℝ) + 1 + ℓ / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) 0 := by
    rw [hUe, vec_smul]; apply Lam_add_eq F <;> ring
  rw [hUlam] at hE
  have hlb := hword (z, idx) hidx _ _ (by positivity) (by linarith) hℓ hE
  have hU1 : U = vec F 1 0 := by rw [hUe, hlb, div_self hb0.ne', one_smul]
  have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hang
  rcases hang with hz | hz | hz
  · obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hz
    have hWc : ‖W‖ = (f : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hlb] at h1; exact absurd h1 hbc'
    have hs2 : cross (vec F 1 0) (vec F 0 1) * cross (vec F 1 0) (vec F (1 + cb e f) (-1)) < 0 := by
      rw [cross_vec, cross_vec]; nlinarith
    have hr := ident hmz hUW hU1 (by intro h; rw [h, norm_zero] at hU0n; linarith)
      (by have := side_of_across hS hU0 hside hs2; rwa [hU1] at this)
      (by rw [hWc, norm_vec_01]) (by rw [hopp, dist_add_vec, sub_zero, zero_sub, norm_vec_1m1])
    refine ⟨z, ?_⟩
    rw [hr, Lam_add_eq F rfl (add_zero _), Lam_add_eq F (add_zero _) rfl]
    simp only [Up, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
  · exfalso
    obtain ⟨hn, -⟩ := (corner_dataH F hmz hUW).1 hz
    rcases hn with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hℓdef, hlb] at h1; exact hab h1.symm
    · rw [hℓdef, hlb] at h1; exact hbc' h1
  · exfalso
    rcases mem_of_card_two h0U g0 gU cG hz with rfl | rfl
    · exact ne_of_flank_lam F FC hmz hUW hS hU0 r0 (d1 := -1) (e1 := 0) (d2 := cb e f) (e2 := -1)
        (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by linarith)
        (fun S' hS' h1 h2 => by linarith) rfl
    · exact ne_of_flank_lam F FC hmz hUW hS hU0 rU (d1 := -1) (e1 := 0) (d2 := -1) (e2 := 1)
        (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by linarith)
        (fun S' hS' h1 h2 => by linarith) rfl

/-! ## §7 `N_q` seeds `C(q, q)` -/

/-- `N_q`'s `b`-edge `[qP′, qP′ + b·uL]` is a right-side edge of `L_q` (its third vertex
`V + (q−1)(P′ − A)` has `col = q − 1 + (1 + c/b) > q`). -/
theorem Nq_seed (L : LFrame F) (q : ℕ) (hN : Present D (Nq F q)) :
    ∃ ε ∈ rightChain F q, EdgeIs D ε (Lam F q 0)
      (Lam F q (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) := by
  have FC := L.FC
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  obtain ⟨hcb0, -⟩ := cb_pos F
  obtain ⟨iN, hr⟩ := hN
  rw [Nq_eq F FC] at hr
  have hq : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  have hP : Lam F q 0 ∈ Set.range (D.tile iN).pts := by rw [hr]; exact mem3_2
  have hQ : Lam F q (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) ∈ Set.range (D.tile iN).pts := by
    rw [hr]; exact mem3_3
  obtain ⟨m, hm⟩ := edge_idx hP hQ (Lam_ne F FC (Or.inr (by intro h; linarith)))
  have hall : ∀ k, col F F.A + q ≤ col F ((D.tile iN).pts k) := by
    intro k
    have : (D.tile iN).pts k ∈ Set.range (D.tile iN).pts := ⟨k, rfl⟩
    rw [hr] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h <;> rw [h, col_Lam F FC] <;> linarith
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(iN, m), mem_rightChain F FC h1 h2 hall, by simp only [EdgeIs]; rw [h1, h2]⟩
  · exact ⟨(iN, m), mem_rightChain F FC h1 h2 hall,
      by simp only [EdgeIs]; rw [h1, h2, Set.pair_comm]⟩

/-- **The start of a right-side covering** (generalizes `start_of_up`): a right-side edge of `L_x`
from `Λ(x, 0)` down to `Λ(x, ℓ)` means no right-side edge passes through `Λ(x, 0)`. -/
theorem start_of_edge (L : LFrame F) (x ℓ : ℝ) (hℓ : 0 < ℓ) {ε : Fin N × Fin 3}
    (hε : ε ∈ rightChain F x) (hE : EdgeIs D ε (Lam F x 0) (Lam F x ℓ)) :
    ¬ RStr F x (Lam F x 0) := by
  classical
  have FC := L.FC
  obtain ⟨-, -, hc0, -, -⟩ := consts F
  have hu0 : F.uL ≠ 0 := TraceCovering.ne_zero_of_norm F.huL
  have hg : col F ≠ 0 := col_ne F FC
  have hg' : (-(col F) : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg (neg_eq_zero.mp h)
  have hgd : ∀ y, (-(col F)) y = -(col F (Lam F x 0)) ↔ col F y = col F (Lam F x 0) :=
    TraceCovering.neg_iff
  have hgu : col F F.uL = 0 := col_uL F FC
  have hpt : ∀ y : ℝ, Lam F x y = Lam F x 0 + (y * (f : ℝ) ^ 2) • F.uL := fun y => Lam_line F _ y
  have hpq : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
    pts_ne _ (TraceCovering.fin3_succ_ne ε.2)
  have hℓc : 0 < ℓ * (f : ℝ) ^ 2 := by positivity
  have hedge : (D.tile ε.1).edge ε.2 = segment ℝ (Lam F x 0 + (0 : ℝ) • F.uL)
      (Lam F x 0 + (ℓ * (f : ℝ) ^ 2) • F.uL) := by
    have e0 : Lam F x 0 + (0 : ℝ) • F.uL = Lam F x 0 := by rw [zero_smul, add_zero]
    rw [Tri.edge, e0, ← hpt ℓ]
    rcases pair_cases hE hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, segment_symm]
  have hin := fun y => TraceCovering.mem_edge_iff hgd hg rfl hgu hu0 hε y
  have hX1 := (hin 0).mp (by rw [hedge]; exact left_mem_segment ℝ _ _)
  have hX2 := (hin (ℓ * (f : ℝ) ^ 2)).mp (by rw [hedge]; exact right_mem_segment ℝ _ _)
  intro hstr
  have hstr' : TraceCovering.Straddled D.toDissection (-(col F)) (-(col F (Lam F x 0)))
      (Lam F x 0 + (0 : ℝ) • F.uL) := by rw [zero_smul, add_zero]; exact hstr
  obtain ⟨ε', hε', hlo, hhi⟩ := (TraceCovering.str_iff hgd hg rfl hgu hu0 0).mp hstr'
  by_cases hεe : ε' = ε
  · subst hεe
    have hlo' := (hin (TraceCovering.lo D.toDissection (Lam F x 0) F.uL ε')).mpr
      ⟨le_rfl, by linarith⟩
    rw [hedge, TraceCovering.segment_param] at hlo'
    obtain ⟨x', hx', hxe⟩ := hlo'
    have := TraceCovering.lm_injective hu0 hxe
    rw [min_eq_left hℓc.le] at hx'
    linarith [hx'.1]
  · have hsub := TraceCovering.meet hg' hgd hg rfl hgu hu0 ε' hε' ε hε hεe
    set δ := min (TraceCovering.hi D.toDissection (Lam F x 0) F.uL ε') (ℓ * (f : ℝ) ^ 2) / 2
      with hδ
    have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hhi hℓc)
    have hδ1 : δ < TraceCovering.hi D.toDissection (Lam F x 0) F.uL ε' := by
      have := min_le_left (TraceCovering.hi D.toDissection (Lam F x 0) F.uL ε') (ℓ * (f : ℝ) ^ 2)
      rw [hδ]; linarith
    have hδ2 : δ ≤ ℓ * (f : ℝ) ^ 2 := by
      have := min_le_right (TraceCovering.hi D.toDissection (Lam F x 0) F.uL ε') (ℓ * (f : ℝ) ^ 2)
      rw [hδ]; linarith
    have := hsub ⟨⟨hlo.le, hhi.le⟩, hX1⟩ ⟨⟨by linarith, hδ1.le⟩, ⟨by linarith [hX1.1], by
      linarith [hX2.2]⟩⟩
    linarith

/-! ## §8 (2) The rows of `q·T₃`, and (3) the kill -/

/-- **The down cells of row `n+1`** (`row_all_gen` + a descending `row_one_gen` from the row end
`Λ(n+1, 0)` on `m₀`), given the cells above, no straight tile at `Λ(n+1, 0)`, and the `γ`-exclusion
there. -/
theorem row_down (L : LFrame F) (n : ℕ) (hnf : n + 2 ≤ f)
    (hUp : ∀ i t, i + t ≤ n → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 1 ≤ n → Present D (Dn F i t))
    (hns : ∀ z, (D.tile z).localAngle (Lam F ((n : ℝ) + 1) 0) ≠ Real.pi ∧
      (D.tile z).localAngle (Lam F ((n : ℝ) + 1) 0) ≠ 2 * Real.pi)
    (hγ0 : ∀ iG : Fin N, Set.range (D.tile iG).pts = Up F n 0 → ∀ z : Fin N, z ≠ iG →
      ∀ (mz : Fin 3) (U W : Plane) (S : ℝ), (D.tile z).pts mz = Lam F ((n : ℝ) + 1) 0 →
      IsFlankPair (D.tile z) mz (Lam F ((n : ℝ) + 1) 0) U W → 0 < S → vec F (-1) 1 = S • U →
      (D.tile z).localAngle (Lam F ((n : ℝ) + 1) 0) ≠ γ) :
    ∀ i t, i + t = n → Present D (Dn F i t) := by
  classical
  have FC := L.FC
  have hnfR : (n : ℝ) + 2 ≤ f := by exact_mod_cast hnf
  have hs0 : ¬ TraceCovering.Straddled D.toDissection (-(lev F))
      (-(lev F F.A + (((n + 1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)))) (Lam F ((n + 1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
    rw [Nat.cast_zero, Nat.cast_succ]; exact nstr_of_ns hns _ _
  have hall := row_all_gen F L (n + 1) 0 (by omega) (by omega)
    (fun i t hi hit => hUp i t (by omega)) hs0
  have key : ∀ k, ∀ i, i + k = n → Present D (Dn F i k) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have hin : i = n := by omega
      rw [hin]
      obtain ⟨iG, hrG⟩ := hUp n 0 (by omega)
      exact row_one_gen F L (n + 1) 0 n 0 le_rfl (by omega) (by omega) hall hrG
        (by rw [Nat.cast_zero]; exact hedge_of_ns hns (vec F (-1) 1))
        (by rw [Nat.cast_zero]; exact hγ0 iG hrG)
    | succ k ih =>
      intro i hi
      obtain ⟨iG, hrG⟩ := hUp i (k + 1) (by omega)
      obtain ⟨iA, hrA⟩ := hDn i k (by omega)
      obtain ⟨iG2, hrG2⟩ := ih (i + 1) (by omega)
      have hik : ((i + k + 1 : ℕ) : ℝ) = n := by exact_mod_cast (by omega : i + k + 1 = n)
      push_cast at hik
      have hYint : Lam F ((i : ℝ) + 1) ((k + 1 : ℕ) : ℝ) ∈ interior D.target.carrier :=
        Lam_interior F FC (by positivity) (by positivity) (by push_cast; linarith)
      have gA : (D.tile iA).localAngle (Lam F ((i : ℝ) + 1) ((k + 1 : ℕ) : ℝ)) = α := by
        rw [Nat.cast_succ]; exact (Dn_angles F hrA).2.2
      have gG : (D.tile iG).localAngle (Lam F ((i : ℝ) + 1) ((k + 1 : ℕ) : ℝ)) = γ :=
        (Up_angles F hrG).2.1
      have gG2 : (D.tile iG2).localAngle (Lam F ((i : ℝ) + 1) ((k + 1 : ℕ) : ℝ)) = γ := by
        rw [Nat.cast_succ]; have := (Dn_angles F hrG2).2.1
        simp only [Nat.cast_add, Nat.cast_one] at this; exact this
      have rG2 : Set.range (D.tile iG2).pts = {Lam F ((i : ℝ) + 1) ((k + 1 : ℕ) : ℝ),
          Lam F ((i : ℝ) + 1 + 1) k, Lam F ((i : ℝ) + 1 + 1) ((k + 1 : ℕ) : ℝ)} := by
        rw [hrG2]; simp only [Dn, Nat.cast_add, Nat.cast_one]
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      have hG12 : iG ≠ iG2 := ne_of_range hrG hrG2 (p := Lam F i ((k + 1 : ℕ) : ℝ))
        (by simp only [Up]; exact mem3_1)
        (by simp only [Dn, Nat.cast_add, Nat.cast_one]
            exact not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
              (Or.inl (by intro h; linarith)))
      obtain ⟨hns', cG⟩ := count_ag F hYint hG12 gA gG gG2
      exact row_one_gen F L (n + 1) 0 i (k + 1) (by omega) (by omega) (by omega) hall hrG
        (hedge_of_ns hns' (vec F (-1) 1))
        (fun z hzG mz U W S hmz hUW hS hU0 hzγ => by
          rcases mem_of_card_two hG12 gG gG2 cG hzγ with h | h
          · exact hzG h
          · exact ne_of_flank_lam F FC hmz hUW hS hU0 rG2 (d1 := 1) (e1 := -1) (d2 := 1)
              (e2 := 0) (by ring) (by push_cast; ring) (by ring) (by ring)
              (fun S' hS' h1 h2 => by linarith) (fun S' hS' h1 h2 => by linarith) h)
  intro i t hit
  exact key t i hit

/-- The counting at the row end `Λ(n+1, 0)` inside the triangle (`n + 1 < q`): the column tiles
`T₂ + (n+1)P′` (`α`), `T₂ + nP′` (`γ`) and `Up n 0` (`γ`). -/
theorem end_col (L : LFrame F) (n : ℕ) (hnf : n + 3 ≤ f) (hc1 : Present D (Col F (n + 1)))
    (hc0 : Present D (Col F n)) (hU : Present D (Up F n 0)) :
    (∀ z, (D.tile z).localAngle (Lam F ((n : ℝ) + 1) 0) ≠ Real.pi ∧
      (D.tile z).localAngle (Lam F ((n : ℝ) + 1) 0) ≠ 2 * Real.pi) ∧
    (∀ iG : Fin N, Set.range (D.tile iG).pts = Up F n 0 → ∀ z : Fin N, z ≠ iG →
      ∀ (mz : Fin 3) (U W : Plane) (S : ℝ), (D.tile z).pts mz = Lam F ((n : ℝ) + 1) 0 →
      IsFlankPair (D.tile z) mz (Lam F ((n : ℝ) + 1) 0) U W → 0 < S → vec F (-1) 1 = S • U →
      (D.tile z).localAngle (Lam F ((n : ℝ) + 1) 0) ≠ γ) := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hnR : (n : ℝ) + 3 ≤ f := by exact_mod_cast hnf
  have hXint : Lam F ((n : ℝ) + 1) 0 ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) le_rfl (by linarith)
  obtain ⟨i1, hr1⟩ := hc1
  obtain ⟨i0, hr0⟩ := hc0
  rw [Col_eq F FC] at hr1 hr0
  push_cast at hr1
  have r1 : Set.range (D.tile i1).pts = {Lam F ((n : ℝ) + 1) 0, Lam F ((n : ℝ) + 1 + 1) 0,
      Lam F ((n : ℝ) + 1 + 1 + cb e f) (-1)} := by
    rw [hr1]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have r0 : Set.range (D.tile i0).pts = {Lam F ((n : ℝ) + 1) 0, Lam F n 0,
      Lam F ((n : ℝ) + 1 + cb e f) (-1)} := by
    rw [hr0]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have g1 : (D.tile i1).localAngle (Lam F ((n : ℝ) + 1) 0) = α := by
    apply (angle_of_range F r1).1
    rw [dist_Lam, show (n : ℝ) + 1 + 1 - ((n : ℝ) + 1 + 1 + cb e f) = -cb e f by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-cb e f) 1 = - vec F (cb e f) (-1) by rw [vec_neg]; norm_num, norm_neg, norm_VP]
  have g0 : (D.tile i0).localAngle (Lam F ((n : ℝ) + 1) 0) = γ := by
    apply (angle_of_range F r0).2.2
    rw [dist_Lam, show (n : ℝ) - ((n : ℝ) + 1 + cb e f) = -(1 + cb e f) by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  have key : ∀ iG : Fin N, Set.range (D.tile iG).pts = Up F n 0 →
      (D.tile iG).localAngle (Lam F ((n : ℝ) + 1) 0) = γ ∧ i0 ≠ iG := by
    intro iG hrG
    refine ⟨by have := (Up_angles F hrG).2.1; simp only [Nat.cast_zero] at this; exact this, ?_⟩
    have rU : Set.range (D.tile iG).pts = {Lam F ((n : ℝ) + 1) 0, Lam F n 0, Lam F n 1} := by
      rw [hrG]; simp only [Up, Nat.cast_zero, zero_add]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    exact (ne_of_range rU r0 (p := Lam F n 1) mem3_3
      (not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)))).symm
  obtain ⟨iU, hrU⟩ := hU
  obtain ⟨gU, h0U⟩ := key iU hrU
  refine ⟨(count_ag F hXint h0U g1 g0 gU).1, fun iG hrG z hzG mz U W S hmz hUW hS hU0 hzγ => ?_⟩
  obtain ⟨gG, h0G⟩ := key iG hrG
  obtain ⟨-, cG⟩ := count_ag F hXint h0G g1 g0 gG
  rcases mem_of_card_two h0G g0 gG cG hzγ with h | h
  · exact ne_of_flank_lam F FC hmz hUW hS hU0 r0 (d1 := -1) (e1 := 0) (d2 := cb e f) (e2 := -1)
      (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by linarith)
      (fun S' hS' h1 h2 => by nlinarith) h
  · exact hzG h

/-- The counting at `qP′ = Λ(q'+1, 0)`: `T₂ + q'P′`, `N_{q'+1}` and `Up q' 0` present three `γ`'s. -/
theorem end_N (L : LFrame F) (q' : ℕ) (hqf : q' + 2 ≤ f) (hc0 : Present D (Col F q'))
    (hN : Present D (Nq F (q' + 1))) (hU : Present D (Up F q' 0)) :
    (∀ z, (D.tile z).localAngle (Lam F ((q' : ℝ) + 1) 0) ≠ Real.pi ∧
      (D.tile z).localAngle (Lam F ((q' : ℝ) + 1) 0) ≠ 2 * Real.pi) ∧
    (∀ iG : Fin N, Set.range (D.tile iG).pts = Up F q' 0 → ∀ z : Fin N, z ≠ iG →
      ∀ (mz : Fin 3) (U W : Plane) (S : ℝ), (D.tile z).pts mz = Lam F ((q' : ℝ) + 1) 0 →
      IsFlankPair (D.tile z) mz (Lam F ((q' : ℝ) + 1) 0) U W → 0 < S → vec F (-1) 1 = S • U →
      (D.tile z).localAngle (Lam F ((q' : ℝ) + 1) 0) ≠ γ) := by
  classical
  have FC := L.FC
  obtain ⟨-, hb0, hc0', -, -⟩ := consts F
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hqR : (q' : ℝ) + 2 ≤ f := by exact_mod_cast hqf
  have hXint : Lam F ((q' : ℝ) + 1) 0 ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) le_rfl (by linarith)
  have hbc : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  obtain ⟨i0, hr0⟩ := hc0
  obtain ⟨iN, hrN⟩ := hN
  rw [Col_eq F FC] at hr0
  rw [Nq_eq F FC] at hrN
  push_cast at hrN
  have r0 : Set.range (D.tile i0).pts = {Lam F ((q' : ℝ) + 1) 0, Lam F q' 0,
      Lam F ((q' : ℝ) + 1 + cb e f) (-1)} := by
    rw [hr0]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have rN : Set.range (D.tile iN).pts = {Lam F ((q' : ℝ) + 1) 0,
      Lam F ((q' : ℝ) + 1 + cb e f) (-1),
      Lam F ((q' : ℝ) + 1) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)} := by
    rw [hrN]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have g0 : (D.tile i0).localAngle (Lam F ((q' : ℝ) + 1) 0) = γ := by
    apply (angle_of_range F r0).2.2
    rw [dist_Lam, show (q' : ℝ) - ((q' : ℝ) + 1 + cb e f) = -(1 + cb e f) by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  have gN : (D.tile iN).localAngle (Lam F ((q' : ℝ) + 1) 0) = γ := by
    apply (angle_of_range F rN).2.2
    rw [dist_Lam, show (q' : ℝ) + 1 + cb e f - ((q' : ℝ) + 1) = cb e f by ring,
      show (-1 : ℝ) - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2
        = -1 - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 by ring, norm_MN]
  have h0N : i0 ≠ iN := ne_of_range r0 rN (p := Lam F q' 0) mem3_2
    (not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
      (Or.inl (by intro h; linarith)))
  have key : ∀ iG : Fin N, Set.range (D.tile iG).pts = Up F q' 0 →
      (D.tile iG).localAngle (Lam F ((q' : ℝ) + 1) 0) = γ ∧ i0 ≠ iG ∧ iN ≠ iG := by
    intro iG hrG
    refine ⟨by have := (Up_angles F hrG).2.1; simp only [Nat.cast_zero] at this; exact this, ?_, ?_⟩
    · have rU : Set.range (D.tile iG).pts = {Lam F ((q' : ℝ) + 1) 0, Lam F q' 0, Lam F q' 1} := by
        rw [hrG]; simp only [Up, Nat.cast_zero, zero_add]
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact (ne_of_range rU r0 (p := Lam F q' 1) mem3_3
        (not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)))).symm
    · have rU : Set.range (D.tile iG).pts = {Lam F ((q' : ℝ) + 1) 0, Lam F q' 0, Lam F q' 1} := by
        rw [hrG]; simp only [Up, Nat.cast_zero, zero_add]
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      exact (ne_of_range rU rN (p := Lam F q' 0) mem3_2
        (not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
          (Or.inl (by intro h; linarith)))).symm
  obtain ⟨iU, hrU⟩ := hU
  obtain ⟨gU, h0U, hNU⟩ := key iU hrU
  refine ⟨(count_ggg F hXint h0N h0U hNU g0 gN gU).1,
    fun iG hrG z hzG mz U W S hmz hUW hS hU0 hzγ => ?_⟩
  obtain ⟨gG, h0G, hNG⟩ := key iG hrG
  rcases (count_ggg F hXint h0N h0G hNG g0 gN gG).2 z hzγ with h | h | h
  · exact ne_of_flank_lam F FC hmz hUW hS hU0 r0 (d1 := -1) (e1 := 0) (d2 := cb e f) (e2 := -1)
      (by ring) (by ring) (by ring) (by ring) (fun S' hS' h1 h2 => by linarith)
      (fun S' hS' h1 h2 => by nlinarith) h
  · exact ne_of_flank_lam F FC hmz hUW hS hU0 rN (d1 := cb e f) (e1 := -1) (d2 := 0)
      (e2 := ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2) (by ring) (by ring) (by ring) (by ring)
      (fun S' hS' h1 h2 => by nlinarith) (fun S' hS' h1 h2 => by linarith) h
  · exact hzG h

/-- **(2) The triangle `q·T₃` is forced** (PK·a step 2): given the column `T₂ + jP′`, `j < q`, and
`N_q`, for every `1 ≤ n ≤ q` every up cell `Up i t` with `i + t + 1 ≤ n` and every down cell
`Dn i t` with `i + t + 2 ≤ n` is a tile.  Row by row: the down cells by `row_down` (end counting
`end_col`), the leg slot by `slot_leg` (**m = 1**), the interior slots by `slot_int` with
`RW(i)` (`rw_frame`) killing the swaps, the matched slot by `matched_slot` (**m = 1**:
`b^q`). -/
theorem triangle (L : LFrame F) (q : ℕ) (hq1 : 1 ≤ q) (hqf : q + 1 ≤ f)
    (hcol : ∀ j < q, Present D (Col F j)) (hN : Present D (Nq F q)) :
    ∀ n, 1 ≤ n → n ≤ q → (∀ i t, i + t + 1 ≤ n → Present D (Up F i t)) ∧
      (∀ i t, i + t + 2 ≤ n → Present D (Dn F i t)) := by
  have FC := L.FC
  have hword := matched_word F L q hq1 hqf hcol hN
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn1 hnq
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · refine ⟨fun i t hit => ?_, fun i t hit => by omega⟩
      have hi : i = 0 := by omega
      have ht : t = 0 := by omega
      rw [hi, ht]
      obtain ⟨i3, h3⟩ := F.hT3
      refine ⟨i3, ?_⟩
      rw [h3]; simp only [Up, Nat.cast_zero, zero_add]
      rw [Lam_zero_zero, ← P_eq F]
      simp only [Lam, vec, v, zero_smul, zero_add, one_smul]
    · obtain ⟨hU, hD⟩ := ih (by omega) (by omega)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      -- (a) the down cells of row `n' + 1`
      obtain ⟨hns, hγ0⟩ := end_col F L n' (by omega) (hcol (n' + 1) (by omega)) (hcol n' (by omega))
        (hU n' 0 (by omega))
      have hDnew := row_down F L n' (by omega) (fun i t h => hU i t (by omega))
        (fun i t h => hD i t (by omega)) hns hγ0
      -- (b) the up cells of band `B_{n'+1}`
      have hUnew : ∀ i t, i + t = n' + 1 → Present D (Up F i t) := by
        intro i t hit
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · have ht : t = n' + 1 := by omega
          rw [ht]
          exact slot_leg F L n' (by omega) (hU 0 n' (by omega)) (hDnew 0 n' (by omega))
        · rcases Nat.eq_zero_or_pos t with rfl | ht0
          · have hi : i = n' + 1 := by omega
            rw [hi]
            exact matched_slot F L q n' (by omega) hqf hword (hcol (n' + 1) (by omega))
              (hcol n' (by omega)) (hU n' 0 (by omega))
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
            rcases slot_int F L i' t' (by omega) (hD i' t' (by omega)) (hU (i' + 1) t' (by omega))
                (hDnew i' (t' + 1) (by omega)) (hU i' (t' + 1) (by omega))
                (hDnew (i' + 1) t' (by omega)) with h | hXs
            · exact h
            · exfalso
              -- the swap seeds `C(i'+1, n'+1)`: killed by `RW(i'+1)`
              apply rw_frame F L (i' + 1) (n' + 1) (by omega) (by omega) (by omega)
              refine ⟨fun i t hi ht => ⟨hU i t ht, ?_⟩, ?_, ?_⟩
              · rcases Nat.lt_or_ge (i + t + 1) (n' + 1) with h | h
                · exact hD i t (by omega)
                · exact hDnew i t (by omega)
              · exact start_of_up F L (i' + 1) (hU (i' + 1) 0 (by omega))
              · obtain ⟨ε, hε, hE⟩ := seed_of_Xs F L _ _ hXs
                refine ⟨ε, by push_cast; exact hε, (t' : ℝ) + 1, by positivity, ?_, by
                  push_cast; exact hE⟩
                have : ((i' + 1 + (t' + 1) : ℕ) : ℝ) = ((n' + 1 : ℕ) : ℝ) := by rw [hit]
                push_cast at this ⊢; linarith
      refine ⟨fun i t hit => ?_, fun i t hit => ?_⟩
      · rcases Nat.lt_or_ge (i + t + 1) (n' + 1 + 1) with h | h
        · exact hU i t (by omega)
        · exact hUnew i t (by omega)
      · rcases Nat.lt_or_ge (i + t + 2) (n' + 1 + 1) with h | h
        · exact hD i t (by omega)
        · exact hDnew i t (by omega)

/-- **PK·a — THE LEVEL MIRROR GIVEN THE COLUMN, frame form — PROVED.**  In the apex frame of a
dissection satisfying `LFrame` (cone coordinates + `b`-free leg), for `1 ≤ q ≤ f − 1`, the column
`T₂ + jP′` (`0 ≤ j ≤ q − 1`) and the level mirror `N_q = M₁ + (q−1)P′` are not all tiles.
(report_exact_forms.md S2; `q = 1` is R2.)  Step 3: at `qP′` three `γ`'s (`end_N`), the row-`q`
down cells (`row_down`), and `N_q`'s `b`-edge down `L_q` (`Nq_seed`, `start_of_edge`) give `C(q, q)`,
which `RW(q)` (`rw_frame`) forbids.  The `m = 1` inputs: `b^q` on `m₀` (`Inflation.b_side_rigid`),
the row words `a^n` (`a_side_no_b`, `a_side_rigid`), Lemma A (`c_side_no_b`), the `b`-free leg. -/
theorem pka_frame (L : LFrame F) (q : ℕ) (hq1 : 1 ≤ q) (hqf : q + 1 ≤ f)
    (hcol : ∀ j < q, Present D (Col F j)) (hN : Present D (Nq F q)) : False := by
  have FC := L.FC
  obtain ⟨hU, hD⟩ := triangle F L q hq1 hqf hcol hN q hq1 le_rfl
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨hns, hγ0⟩ := end_N F L q' (by omega) (hcol q' (by omega)) hN (hU q' 0 (by omega))
  have hDq := row_down F L q' (by omega) (fun i t h => hU i t (by omega))
    (fun i t h => hD i t (by omega)) hns hγ0
  obtain ⟨ε, hε, hE⟩ := Nq_seed F L (q' + 1) hN
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  have hbc : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  apply rw_frame F L (q' + 1) (q' + 1) hq1 le_rfl hqf
  refine ⟨fun i t hi ht => ⟨hU i t ht, ?_⟩, start_of_edge F L _ _ hbc hε hE,
    ⟨ε, hε, 0, le_rfl, by simp, by rw [zero_add]; exact hE⟩⟩
  rcases Nat.lt_or_ge (i + t + 1) (q' + 1) with h | h
  · exact hD i t (by omega)
  · exact hDq i t (by omega)

/-- **PK·a FOR EVERY APEX FRAME OF A REAL `m = 1` DISSECTION — PROVED.** -/
theorem pka_real_all {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k)
    (FC : ApexPlacement.FrameCoords F) (q : ℕ) (hq1 : 1 ≤ q) (hqf : q + 1 ≤ f)
    (hcol : ∀ j < q, Present D (Col F j)) : ¬ Present D (Nq F q) :=
  fun hN => pka_frame F (lframe_real F h FC) q hq1 hqf hcol hN

/-- **PK·a — THE LEVEL MIRROR IS IMPOSSIBLE GIVEN THE COLUMN, FOR EVERY REAL `m = 1` DISSECTION —
PROVED.**  Every congruent dissection of the `m = 1` base-β target (coprime `2 ≤ e ≤ f − 2`,
`M1Data`) carries its apex frame `F`, and for every `1 ≤ q ≤ f − 1`, if `T₂ + jP′` is a tile for
every `j < q`, then `N_q` is not a tile. -/
theorem pka_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, ApexPlacement.FrameCoords F ∧
      ∀ q : ℕ, 1 ≤ q → q + 1 ≤ f → (∀ j < q, Present D (Col F j)) → ¬ Present D (Nq F q) := by
  obtain ⟨F, FC⟩ := ApexLegWord.exists_hframe_coords_m1 D h.hco h.he h.hef h.hM h.hAng k
    h.hcorner h.hβ1 h.hβ2 h.hleg1 h.hleg2 h.hbase
  exact ⟨F, FC, fun q hq1 hqf hcol => pka_real_all F h FC q hq1 hqf hcol⟩

/-- **PK·a with the mirror given as the paper gives it**: `M₁` = the mirror image of `T₂`'s apex `A`
across its `a`-edge `VP′` (`IsMirror A V P′ M`), `N_q = M₁ + (q−1)P′ = {V, P′, M} + (q−1)(P′ − A)`
(the identification `M = P′ + b·uL` is `ApexR2Frame.mirror_eq`). -/
theorem pka_mirror (L : LFrame F) {M : Plane} (hMir : IsMirror F.A F.V F.P M) (q : ℕ) (hq1 : 1 ≤ q)
    (hqf : q + 1 ≤ f) (hcol : ∀ j < q, Present D (Col F j)) :
    ¬ Present D {F.V + ((q : ℝ) - 1) • (F.P - F.A), F.P + ((q : ℝ) - 1) • (F.P - F.A),
      M + ((q : ℝ) - 1) • (F.P - F.A)} := by
  intro hN
  apply pka_frame F L q hq1 hqf hcol
  rw [ApexR2Frame.mirror_eq F L.FC hMir, add_right_comm] at hN
  exact hN

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.row_all_gen
#print axioms Erdos634.Draft.RowWallReal.row_one_gen
#print axioms Erdos634.Draft.RowWallReal.V_eq
#print axioms Erdos634.Draft.RowWallReal.matched_word
#print axioms Erdos634.Draft.RowWallReal.matched_slot
#print axioms Erdos634.Draft.RowWallReal.start_of_edge
#print axioms Erdos634.Draft.RowWallReal.Nq_seed
#print axioms Erdos634.Draft.RowWallReal.row_down
#print axioms Erdos634.Draft.RowWallReal.end_col
#print axioms Erdos634.Draft.RowWallReal.end_N
#print axioms Erdos634.Draft.RowWallReal.triangle
#print axioms Erdos634.Draft.RowWallReal.pka_frame
#print axioms Erdos634.Draft.RowWallReal.pka_real_all
#print axioms Erdos634.Draft.RowWallReal.pka_real
#print axioms Erdos634.Draft.RowWallReal.pka_mirror
