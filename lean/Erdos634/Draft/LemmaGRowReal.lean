-- Draft/LemmaGRowReal.lean — R8 (Lemma G at level `k`, (private working notes, not included) §5.8,
-- review_S2B, review2_R8S4) ON THE ROW SIDE, for real `m = 1` dissections in the apex frame: row `k`
-- of the `Λ₃` triangle, with rigid end `kP′`, has far side `a^k`; the tile across each of its `a`-edges
-- is the half-turn (`Z₀`-translate) or the mirror; and any mirror forces the mirror `G_k` at `kP′`
-- (PROP).  The anti-diagonal `AD_k` half of R8 and the six-fill catalogue at `kP′` are NOT here.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): MirrorLevelQReal olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/LemmaGRowReal.lean'
import Erdos634.Draft.MirrorLevelQReal

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

include F in
/-- **Corner data at a `γ` corner** (the `γ` clause missing from `corner_dataH`): flanks `{a, b}`,
opposite side `c`. -/
theorem corner_dataG {i : Fin N} {m : Fin 3} {x U W : Plane} (hm : (D.tile i).pts m = x)
    (hUW : IsFlankPair (D.tile i) m x U W) (hg : (D.tile i).localAngle x = γ) :
    ((‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      (‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
      dist (x + U) (x + W) = (f : ℝ) ^ 2 := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) F.hM.hs0 F.hM.hs1 F.hM.hs2 m
  have hL := localAngle_of_oppSideE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2
    F.hM.hα' F.hM.hβ' F.hM.hγ' i m
  rw [hm] at hP hL
  have hAD := F.hAng
  have hα := hAD.hα
  have hβ := hAD.hβ
  have hγd := hAD.hγdef
  have hαβ := hAD.hαβ
  obtain ⟨e1, e2, e3⟩ := hL
  have hx : ∀ q : Fin 3, ‖(D.tile i).pts q - x‖ = dist ((D.tile i).pts q) x :=
    fun q => (dist_eq_norm _ _).symm
  have hy : ∀ q : Fin 3, x + ((D.tile i).pts q - x) = (D.tile i).pts q := fun q => by abel
  unfold NearBaseBridge.Perm3 at hP
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hx, hx, hy, hy]
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    first
      | exact ⟨Or.inl ⟨h1, h2⟩, h3⟩
      | exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg; rw [hγd] at h4; linarith)
      | (exfalso; have h4 := (e2 h3).symm.trans hg; rw [hγd] at h4; linarith)
  · rw [hx, hx, hy, hy, dist_comm ((D.tile i).pts (m + 2)) ((D.tile i).pts (m + 1))]
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    first
      | exact ⟨Or.inl ⟨h2, h1⟩, h3⟩
      | exact ⟨Or.inr ⟨h2, h1⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg; rw [hγd] at h4; linarith)
      | (exfalso; have h4 := (e2 h3).symm.trans hg; rw [hγd] at h4; linarith)

set_option maxHeartbeats 1000000 in
/-- **R8 on a row, one junction: the half-turn or the mirror.**  At `Y = Λ(i+1, t)` on row `J + T`
with no straight tile through `Y`, the tile across the up cell `Up i t`'s `a`-edge (row flank
`vec(−1,1)`) has an `a`-edge on the row (`hall`, the row word `a^J`), so it presents `β` or `γ` at
`Y`: with `β` it is the half-turn `Dn i t = Z₀ + Λ(i,t)`, with `γ` it is the mirror of `Up i t` across
that edge. -/
theorem row_one_R8 (L : LFrame F) (J T i t : ℕ) (hi : i + 1 ≤ J) (hit : i + 1 + t = J + T)
    (hf : J + T + 1 ≤ f)
    (hall : ∀ ε ∈ rowChain F ((J : ℝ) + T), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (J : ℝ) →
      p + q = (J : ℝ) + T →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f)
    {iG : Fin N} (hrG : Set.range (D.tile iG).pts = Up F i t)
    (hns : ∀ z, (D.tile z).localAngle (Lam F ((i : ℝ) + 1) (t : ℝ)) ≠ Real.pi ∧
      (D.tile z).localAngle (Lam F ((i : ℝ) + 1) (t : ℝ)) ≠ 2 * Real.pi) :
    Present D (Dn F i t) ∨ ∃ M : Plane, IsMirror (Lam F i t) (Lam F ((i : ℝ) + 1) t)
      (Lam F i ((t : ℝ) + 1)) M ∧ Present D {Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1), M} := by
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
  · exact (hedge_of_ns hns (vec F (-1) 1) z m' hm0 hmpos hcr).elim
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
    left; refine ⟨z, ?_⟩
    rw [hr, Lam_add_eq F (show (i : ℝ) + 1 + -1 = i by ring) rfl,
      Lam_add_eq F (add_zero _) rfl]
    simp only [Dn]
  · -- `γ` at `Y`: the mirror of `Up i t` across its `a`-edge
    right
    obtain ⟨hn, hopp⟩ := corner_dataG F hmz hUW hz
    have hWb : ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rcases hn with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · rw [hℓdef, hla] at h1; exact absurd h1 hab
    refine ⟨Lam F ((i : ℝ) + 1) (t : ℝ) + W, ⟨?_, ?_, ?_⟩, z, ?_⟩
    · intro h
      have := congrArg (lev F) h
      rw [map_add, lev_Lam F FC, lev_Lam F FC] at this
      linarith
    · rw [dist_eq_norm, add_sub_cancel_left, hWb, dist_Lam,
        show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring, sub_self, norm_vec_m10]
    · have eY : Lam F i ((t : ℝ) + 1) = Lam F ((i : ℝ) + 1) (t : ℝ) + U := by
        rw [hU1]; exact (Lam_add_eq F (by ring) (by ring)).symm
      rw [dist_Lam F (i : ℝ) (t : ℝ) (i : ℝ) ((t : ℝ) + 1), sub_self,
        show (t : ℝ) - ((t : ℝ) + 1) = -1 by ring,
        show vec F 0 (-1) = - vec F 0 1 by rw [vec_neg]; norm_num, norm_neg, norm_vec_01, eY,
        dist_comm, hopp]
    · rw [ApexPlacement.range_of_flank hmz hUW, hU1,
        Lam_add_eq F (show (i : ℝ) + 1 + -1 = i by ring) (show (t : ℝ) + 1 = (t : ℝ) + 1 from rfl)]


/-- The mirror of the up cell `Up i t = T₃ + Λ(i,t)` across its `a`-edge `[Λ(i+1,t), Λ(i,t+1)]` is a
tile (`γ` at `Λ(i+1,t)`, `β` at `Λ(i,t+1)`; at `(i,t) = (k−1,0)` this is `G_k`). -/
def MirUp (F : HFrame D e f α β γ) (i t : ℕ) : Prop :=
  ∃ M : Plane, IsMirror (Lam F i t) (Lam F ((i : ℝ) + 1) t) (Lam F i ((t : ℝ) + 1)) M ∧
    Present D {Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1), M}

include F in
/-- Two distinct `γ`'s at an interior point leave no room for a straight tile. -/
theorem count_gg {x : Plane} (hx : x ∈ interior D.target.carrier) {i1 i2 : Fin N} (h12 : i1 ≠ i2)
    (g1 : (D.tile i1).localAngle x = γ) (g2 : (D.tile i2).localAngle x = γ) :
    ∀ z, (D.tile z).localAngle x ≠ Real.pi ∧ (D.tile z).localAngle x ≠ 2 * Real.pi := by
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hx
  have cG := card_two h12 g1 g2
  exact fun z => ⟨fun h => by have := card_one h; omega, fun h => by have := card_one h; omega⟩

/-- The mirror tile's angles: `γ` at `Λ(i+1,t)`, `β` at `Λ(i,t+1)`. -/
theorem MirUp_angles {i t : ℕ} {M : Plane}
    (hM : IsMirror (Lam F i t) (Lam F ((i : ℝ) + 1) t) (Lam F i ((t : ℝ) + 1)) M) {z : Fin N}
    (hz : Set.range (D.tile z).pts = {Lam F ((i : ℝ) + 1) t, Lam F i ((t : ℝ) + 1), M}) :
    (D.tile z).localAngle (Lam F ((i : ℝ) + 1) t) = γ ∧
      (D.tile z).localAngle (Lam F i ((t : ℝ) + 1)) = β := by
  obtain ⟨-, h1, h2⟩ := hM
  have hz2 : Set.range (D.tile z).pts = {Lam F i ((t : ℝ) + 1), M, Lam F ((i : ℝ) + 1) t} := by
    rw [hz]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨(angle_of_range F hz).2.2 ?_, (angle_of_range F hz2).2.1 ?_⟩
  · rw [dist_comm, h2, dist_Lam, sub_self, show (t : ℝ) - ((t : ℝ) + 1) = -1 by ring,
      show vec F 0 (-1) = - vec F 0 1 by rw [vec_neg]; norm_num, norm_neg, norm_vec_01]
  · rw [h1, dist_Lam, show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring, sub_self, norm_vec_m10]

/-- **R8 ON ROW `K = k + 1` — PROVED (clauses (1)–(3) of `proof_H_empty.md` §5.8, row half).**
(Indexing: the level is `K = k + 1`, `kP′` of the paper is `Λ(k+1, 0)` here.)  Given the triangle
`K·T₃` (`Up i t`, `i + t + 1 ≤ K`; `Dn i t`, `i + t + 2 ≤ K`) and `T₂ + (K−1)P′ = Col k` (so the level
corner `Λ(K, 0)` carries two `γ`'s and is rigid), with `K ≤ f − 1`:
(1) the far (lower) side of row `K` from `Λ(K,0)` to the leg is `a^K`: every lower edge leaving a row
point along the row is an `a`-edge (**m = 1**: `Inflation.a_side_no_b`, `a_side_rigid`, `K < f`;
at N = 44 row 2's far side is one `c`-edge, `2a = c`);
(2) the tile across each `a`-edge `[Λ(i+1,t), Λ(i,t+1)]` of the row is the half-turn `Dn i t` or the
mirror of `Up i t` (descending from `kP′`, the previous junction's tile leaves no straight tile);
(3) PROP: a mirror anywhere on the row forces the mirror `G_K` of `T₃ + (K−1)P′ = Up k 0` at `Λ(K,0)`
(a half-turn beside a mirror puts `2γ` below a row point closed to `π` above). -/
theorem r8_row (L : LFrame F) (k : ℕ) (hkf : k + 2 ≤ f)
    (hUp : ∀ i t, i + t + 1 ≤ k + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ k + 1 → Present D (Dn F i t))
    (hcol : Present D (Col F k)) :
    (∀ ε ∈ rowChain F ((k : ℝ) + 1), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (k : ℝ) + 1 →
      p + q = (k : ℝ) + 1 →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f) ∧
    (∀ i t, i + t = k → Present D (Dn F i t) ∨ MirUp F i t) ∧
    (∀ i t, i + t = k → MirUp F i t → MirUp F k 0) := by
  classical
  have FC := L.FC
  obtain ⟨hcb0, -⟩ := cb_pos F
  have hkR : (k : ℝ) + 2 ≤ f := by exact_mod_cast hkf
  -- `kP′ = Λ(k+1, 0)`: two `γ`'s (`T₂ + kP′`… i.e. the column tile `Col k`, and `Up k 0`)
  have hXint : Lam F ((k : ℝ) + 1) 0 ∈ interior D.target.carrier :=
    Lam_interior F FC (by positivity) le_rfl (by linarith)
  obtain ⟨i0, hr0⟩ := hcol
  rw [Col_eq F FC] at hr0
  have r0 : Set.range (D.tile i0).pts = {Lam F ((k : ℝ) + 1) 0, Lam F k 0,
      Lam F ((k : ℝ) + 1 + cb e f) (-1)} := by
    rw [hr0]; ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have g0 : (D.tile i0).localAngle (Lam F ((k : ℝ) + 1) 0) = γ := by
    apply (angle_of_range F r0).2.2
    rw [dist_Lam, show (k : ℝ) - ((k : ℝ) + 1 + cb e f) = -(1 + cb e f) by ring,
      show (0 : ℝ) - -1 = 1 by ring,
      show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
      norm_neg, norm_V]
  obtain ⟨iU, hrU⟩ := hUp k 0 (by omega)
  have gU : (D.tile iU).localAngle (Lam F ((k : ℝ) + 1) 0) = γ := by
    have := (Up_angles F hrU).2.1; simp only [Nat.cast_zero] at this; exact this
  have rU : Set.range (D.tile iU).pts = {Lam F ((k : ℝ) + 1) 0, Lam F k 0, Lam F k 1} := by
    rw [hrU]; simp only [Up, Nat.cast_zero, zero_add]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h0U : i0 ≠ iU := (ne_of_range rU r0 (p := Lam F k 1) mem3_3
    (not_mem3 F FC (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inr (by norm_num)))).symm
  have hns0 := count_gg F hXint h0U g0 gU
  -- (1) the row word
  have hs0 : ¬ TraceCovering.Straddled D.toDissection (-(lev F))
      (-(lev F F.A + (((k + 1 : ℕ) : ℝ) + ((0 : ℕ) : ℝ)))) (Lam F ((k + 1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)) := by
    rw [Nat.cast_zero, Nat.cast_succ]; exact nstr_of_ns hns0 _ _
  have hall := row_all_gen F L (k + 1) 0 (by omega) (by omega)
    (fun i t hi hit => hUp i t (by omega)) hs0
  have hall' : ∀ ε ∈ rowChain F ((k : ℝ) + 1), ∀ p q ℓ : ℝ, 0 < ℓ → p ≤ (k : ℝ) + 1 →
      p + q = (k : ℝ) + 1 →
      EdgeIs D ε (Lam F p q) (Lam F (p - ℓ / ((e : ℝ) * f)) (q + ℓ / ((e : ℝ) * f))) →
      ℓ = (e : ℝ) * f := by
    have := hall; push_cast at this; simpa only [add_zero] using this
  -- (2) the dichotomy at every junction, descending from `kP′`
  have key : ∀ t i, i + t = k → Present D (Dn F i t) ∨ MirUp F i t := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have hik : i = k := by omega
      rw [hik]
      exact row_one_R8 F L (k + 1) 0 k 0 le_rfl (by omega) (by omega) hall hrU
        (by rw [Nat.cast_zero]; exact hns0)
    | succ t ih =>
      intro i hi
      obtain ⟨iG, hrG⟩ := hUp i (t + 1) (by omega)
      obtain ⟨iA, hrA⟩ := hDn i t (by omega)
      obtain ⟨iB, hrB⟩ := hUp (i + 1) t (by omega)
      have hitR : ((i + t + 1 : ℕ) : ℝ) = k := by exact_mod_cast (by omega : i + t + 1 = k)
      push_cast at hitR
      have hYint : Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ) ∈ interior D.target.carrier :=
        Lam_interior F FC (by positivity) (by positivity) (by push_cast; linarith)
      have gA : (D.tile iA).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = α := by
        rw [Nat.cast_succ]; exact (Dn_angles F hrA).2.2
      have gG : (D.tile iG).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ :=
        (Up_angles F hrG).2.1
      have gB : (D.tile iB).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = β := by
        rw [Nat.cast_succ]; have := (Up_angles F hrB).2.2
        simp only [Nat.cast_add, Nat.cast_one] at this; exact this
      have hns : ∀ z, (D.tile z).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) ≠ Real.pi ∧
          (D.tile z).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) ≠ 2 * Real.pi := by
        rcases ih (i + 1) (by omega) with ⟨iD, hrD⟩ | ⟨M, hM, iM, hrM⟩
        · have gD : (D.tile iD).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ := by
            rw [Nat.cast_succ]; have := (Dn_angles F hrD).2.1
            simp only [Nat.cast_add, Nat.cast_one] at this; exact this
          have hGD : iG ≠ iD := ne_of_range hrG hrD (p := Lam F i ((t + 1 : ℕ) : ℝ))
            (by simp only [Up]; exact mem3_1)
            (by simp only [Dn, Nat.cast_add, Nat.cast_one]
                exact not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
                  (Or.inl (by intro h; linarith)))
          exact (count_ag F hYint hGD gA gG gD).1
        · have hrM' : Set.range (D.tile iM).pts = {Lam F ((((i + 1 : ℕ) : ℝ)) + 1) t,
              Lam F ((i + 1 : ℕ) : ℝ) ((t : ℝ) + 1), M} := hrM
          have gM : (D.tile iM).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = β := by
            have := (MirUp_angles F hM hrM').2; push_cast at this ⊢; exact this
          have hBM : iB ≠ iM := by
            refine ne_of_range hrB hrM' (p := Lam F ((i + 1 : ℕ) : ℝ) t) (by simp only [Up]; exact mem3_1) ?_
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            refine ⟨Lam_ne F FC (Or.inl (by push_cast; intro h; linarith)),
              Lam_ne F FC (Or.inr (by intro h; linarith)), fun h => hM.1 h.symm⟩
          obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hYint
          have cB := card_two hBM gB gM
          have cG := card_one gG
          exact fun z => ⟨fun h => by have := card_one h; omega,
            fun h => by have := card_one h; omega⟩
      exact row_one_R8 F L (k + 1) 0 i (t + 1) (by omega) (by omega) (by omega) hall hrG hns
  refine ⟨hall', fun i t hit => key t i hit, ?_⟩
  -- (3) PROP
  intro i t
  induction t generalizing i with
  | zero =>
    intro hit hM
    have hik : i = k := by omega
    rw [hik] at hM; exact hM
  | succ t ih =>
    intro hit hMi
    apply ih (i + 1) (by omega)
    rcases key t (i + 1) (by omega) with ⟨iD, hrD⟩ | hM'
    · exfalso
      obtain ⟨M, hM, iM, hrM⟩ := hMi
      obtain ⟨iG, hrG⟩ := hUp i (t + 1) (by omega)
      obtain ⟨iA, hrA⟩ := hDn i t (by omega)
      have hitR : ((i + t + 1 : ℕ) : ℝ) = k := by exact_mod_cast (by omega : i + t + 1 = k)
      push_cast at hitR
      have hYint : Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ) ∈ interior D.target.carrier :=
        Lam_interior F FC (by positivity) (by positivity) (by push_cast; linarith)
      have gA : (D.tile iA).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = α := by
        rw [Nat.cast_succ]; exact (Dn_angles F hrA).2.2
      have gG : (D.tile iG).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ :=
        (Up_angles F hrG).2.1
      have gD : (D.tile iD).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ := by
        rw [Nat.cast_succ]; have := (Dn_angles F hrD).2.1
        simp only [Nat.cast_add, Nat.cast_one] at this; exact this
      have gM : (D.tile iM).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ :=
        (MirUp_angles F hM hrM).1
      have hGD : iG ≠ iD := ne_of_range hrG hrD (p := Lam F i ((t + 1 : ℕ) : ℝ))
        (by simp only [Up]; exact mem3_1)
        (by simp only [Dn, Nat.cast_add, Nat.cast_one]
            exact not_mem3 F FC (Or.inl (by intro h; linarith)) (Or.inl (by intro h; linarith))
              (Or.inl (by intro h; linarith)))
      have hGM : iG ≠ iM := by
        refine ne_of_range hrG hrM (p := Lam F i ((t + 1 : ℕ) : ℝ)) (by simp only [Up]; exact mem3_1) ?_
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨Lam_ne F FC (Or.inl (by intro h; linarith)),
          Lam_ne F FC (Or.inr (by push_cast; intro h; linarith)), fun h => hM.1 h.symm⟩
      have hDM : iD ≠ iM := by
        refine ne_of_range hrD hrM (p := Lam F (((i + 1 : ℕ) : ℝ) + 1) t) (by simp only [Dn]; exact mem3_1) ?_
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨Lam_ne F FC (Or.inl (by push_cast; intro h; linarith)),
          Lam_ne F FC (Or.inl (by push_cast; intro h; linarith)), fun h => ?_⟩
        -- `M` is at distance `b` from `Λ(i+1, t+1)`, the point `Λ(i+2, t)` at distance `a`
        have h1 := hM.2.1
        rw [← h, dist_Lam, dist_Lam] at h1
        have e1 : ‖vec F ((((i + 1 : ℕ) : ℝ) + 1) - ((i : ℝ) + 1)) ((t : ℝ) - ((t + 1 : ℕ) : ℝ))‖
            = (e : ℝ) * f := by
          push_cast; rw [show (i : ℝ) + 1 + 1 - ((i : ℝ) + 1) = 1 by ring,
            show (t : ℝ) - ((t : ℝ) + 1) = -1 by ring, norm_vec_1m1]
        have e2 : ‖vec F ((i : ℝ) - ((i : ℝ) + 1)) ((t + 1 : ℕ) - ((t + 1 : ℕ) : ℝ))‖
            = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
          rw [show (i : ℝ) - ((i : ℝ) + 1) = -1 by ring, sub_self, norm_vec_m10]
        rw [e1, e2] at h1
        obtain ⟨hab, -, -⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
        exact hab h1
      obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' hYint
      have h3 : 3 ≤ ({j | (D.tile j).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ} :
          Finset (Fin N)).card := by
        have hsub : ({iG, iD, iM} : Finset (Fin N)) ⊆
            ({j | (D.tile j).localAngle (Lam F ((i : ℝ) + 1) ((t + 1 : ℕ) : ℝ)) = γ} :
              Finset (Fin N)) := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact mem_filter_of gG
          · exact mem_filter_of gD
          · exact mem_filter_of gM
        have := Finset.card_le_card hsub
        rwa [Finset.card_eq_three.mpr ⟨iG, iD, iM, hGD, hGM, hDM, rfl⟩] at this
      have := card_one gA
      omega
    · exact hM'

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.corner_dataG
#print axioms Erdos634.Draft.RowWallReal.row_one_R8
#print axioms Erdos634.Draft.RowWallReal.r8_row
