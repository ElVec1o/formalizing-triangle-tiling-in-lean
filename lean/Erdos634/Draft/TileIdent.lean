-- Draft/TileIdent.lean — TILE IDENTIFICATION (blocker F3) and its use at P′ in branch (H).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake; `$S` a full scratch copy of the corpus oleans):
--   lake env lean -o $S/Erdos634/Draft/TraceCovering.olean Erdos634/Draft/TraceCovering.lean
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean -o $S/Erdos634/Draft/HalfTurnR3R4Glue.olean Erdos634/Draft/HalfTurnR3R4Glue.lean'
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean -o $S/Erdos634/Draft/HalfTurnR3R4Order.olean Erdos634/Draft/HalfTurnR3R4Order.lean'
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/TileIdent.lean'
-- (HalfTurnR3R4, NearBaseVertex, NearBase, NearBaseKill, NearBaseBridge, CornerAdjacency oleans as
-- recorded in those files' headers.)
import Erdos634.Draft.HalfTurnR3R4Order

/-!
# Tile identification

`proof_H_empty.md` §4 row ID (blocker F3): "a tile is determined by one corner, its two flank
directions and flank lengths".  The geometric core is elementary and is proved here in the form the
proofs use it: **two points on the same open side of a line `XY`, at the same distances from `X` and
from `Y`, coincide** (`third_vertex_unique`: otherwise `X`, `Y` lie on the perpendicular bisector of the
two points, which then lie on opposite sides).  With congruence to the model (sides `a, b, c` pairwise
distinct) this says: a tile with a known vertex `X`, one flank along a known ray of known length (so
`Y` is known), a known corner type at `X` (so the other two side lengths are known) and its third
vertex on a known side of the flank line, is uniquely determined — orientation up to reflection is
exactly the side condition (`tile_ident`).

Application (`pprime_alpha_ident`, `pprime_band_alpha_T2P`): in branch (H), the band tile at `P′` that
lays a `c`-edge on `ℓ⁺` and presents `α` at `P′` is `T₂ + P′` — the identification half (I) of
`HalfTurnR3R4Glue.pprime_order`'s clause `Lε = c → T₂ + P′` (the note at the foot of
`HalfTurnR3R4Order`).  What that clause still needs is the exclusion of a `β`-corner there.

`lemmaG` (§3): Lemma G steps 3–4 of `proof_H_empty.md` §5.1 in generic form — over any
`CongruentDissection` with model `(ef, f² − e², f²)`, coprime `1 ≤ e < f`: given `T₂`'s `a`-edge
`[V, P′]`, a piercer across the line `VP′` at `V`, no far edge through `P′`, the tile across `[V, P′]`
lays exactly that `a`-edge (TRACE COVERING, `TraceCovering.wall_sum`, + `Inflation.a_unsplittable`)
and is `K = {V, P′, V + P′ − A}` or the mirror of `T₂` (TILE IDENTIFICATION, `third_vertex_unique`).

`lemmaG_frame` (§4): **Lemma G in the `HFrame`, all four steps, WITHOUT assuming branch (H)** — the tile
across `T₂`'s `a`-edge is `K` or the mirror of `T₂`.  Step 1 is `HFrame.V_pierced`
(`HalfTurnR3R4Glue`, TC + Lemma A), step 2 `pprime_vertex_of_mem'` (two `γ` at `P′`, integer angle
count), steps 3–4 `lemmaG`.  Conditional only on the frame (apex placement `thm:pierce(i)` = the
presence fields `hT1, hT2, hT3`, plus the metric fields).

**REDISCOVERY (headline, found after writing §1):** the geometric core of F3 is ALREADY in the
VERIFIED corpus as `SixPlacements.third_vertex` / `six_placements` (in `All.lean`): a tile with a vertex
at `v`, a second vertex on the ray `v + ℝ₊·d` and its third vertex strictly counter-clockwise of `d` is
`placeThird v d ℓ₁ ℓ₂ ℓ₃` for one of the six side permutations.  `third_vertex_unique` below is the
same fact with the side given by a functional instead of the sign of `cross d`; it re-derives it and
adds nothing mathematically.  So blocker F3 ("tile identification", `proof_H_empty.md` §4) was stale
as a MATHEMATICAL gap — what was missing is its use at the named call sites (§2, §3 below).
`dist_sq_coord` duplicates `SixPlacements.dist_sq_coord`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.Draft.TileIdent

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency Erdos634.Draft.HalfTurnR3R4Order

/-! ## §1 The core: the third vertex is determined by two distances and a side -/

theorem dist_sq_coord (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

/-- **Third-vertex uniqueness.**  If `Z`, `Z'` lie strictly on the same side of the line `XY`
(`h X = h Y < h Z, h Z'` for a functional `h`) and `|XZ| = |XZ'|`, `|YZ| = |YZ'|`, then `Z = Z'`. -/
theorem third_vertex_unique (h : Plane →ₗ[ℝ] ℝ) {X Y Z Z' : Plane} (hXY : X ≠ Y)
    (hhXY : h X = h Y) (hZ : h X < h Z) (hZ' : h X < h Z')
    (d1 : dist X Z = dist X Z') (d2 : dist Y Z = dist Y Z') : Z = Z' := by
  by_contra hne
  have e1 : (X 0 - Z 0) ^ 2 + (X 1 - Z 1) ^ 2 = (X 0 - Z' 0) ^ 2 + (X 1 - Z' 1) ^ 2 := by
    rw [← dist_sq_coord, ← dist_sq_coord, d1]
  have e2 : (Y 0 - Z 0) ^ 2 + (Y 1 - Z 1) ^ 2 = (Y 0 - Z' 0) ^ 2 + (Y 1 - Z' 1) ^ 2 := by
    rw [← dist_sq_coord, ← dist_sq_coord, d2]
  have hh : ∀ v : Plane, h v = rotVec h 0 * v 1 - rotVec h 1 * v 0 := fun v => by
    rw [rotVec_spec, Erdos634.Draft.NearBaseVertex.cross_apply]
  rw [hh, hh] at hhXY hZ hZ'
  set r0 := rotVec h 0
  set r1 := rotVec h 1
  -- `p = Y − X`, `w = Z − Z'`, `m = Z + Z' − 2X`
  have hpw : (Y 0 - X 0) * (Z 0 - Z' 0) + (Y 1 - X 1) * (Z 1 - Z' 1) = 0 := by
    linear_combination (e1 - e2) / 2
  have hmw : (Z 0 + Z' 0 - 2 * X 0) * (Z 0 - Z' 0) + (Z 1 + Z' 1 - 2 * X 1) * (Z 1 - Z' 1) = 0 := by
    linear_combination e1
  set p0 := Y 0 - X 0
  set p1 := Y 1 - X 1
  set m0 := Z 0 + Z' 0 - 2 * X 0
  set m1 := Z 1 + Z' 1 - 2 * X 1
  set w0 := Z 0 - Z' 0
  set w1 := Z 1 - Z' 1
  have hc0 : w0 * (p0 * m1 - p1 * m0) = 0 := by linear_combination m1 * hpw - p1 * hmw
  have hc1 : w1 * (p0 * m1 - p1 * m0) = 0 := by linear_combination p0 * hmw - m0 * hpw
  have hw : w0 ≠ 0 ∨ w1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hne
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith [hc.1]
    · simp only [Fin.mk_one, Fin.isValue]; linarith [hc.2]
  have hcross : p0 * m1 - p1 * m0 = 0 := by
    rcases hw with hw | hw
    · exact (mul_eq_zero.mp hc0).resolve_left hw
    · exact (mul_eq_zero.mp hc1).resolve_left hw
  have hrp : r0 * p1 - r1 * p0 = 0 := by linear_combination hhXY.symm
  have hp : p0 ≠ 0 ∨ p1 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hXY
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith [hc.1]
    · simp only [Fin.mk_one, Fin.isValue]; linarith [hc.2]
  have hrm : r0 * m1 - r1 * m0 = 0 := by
    rcases hp with hp | hp
    · have : p0 * (r0 * m1 - r1 * m0) = 0 := by linear_combination r0 * hcross + m0 * hrp
      exact (mul_eq_zero.mp this).resolve_left hp
    · have : p1 * (r0 * m1 - r1 * m0) = 0 := by linear_combination r1 * hcross + m1 * hrp
      exact (mul_eq_zero.mp this).resolve_left hp
  have : (r0 * Z 1 - r1 * Z 0) + (r0 * Z' 1 - r1 * Z' 0) = 2 * (r0 * X 1 - r1 * X 0) := by
    linear_combination hrm
  linarith

/-- **Tile identification (F3).**  A tile whose vertices are `X`, `Y` and a third vertex `Z` strictly
on the `h`-positive side of the line `XY` is the tile `{X, Y, Z₀}` for any `Z₀` on the same side with
`|XZ₀| = |XZ|`, `|YZ₀| = |YZ|`. -/
theorem tile_ident (T : Tri) (h : Plane →ₗ[ℝ] ℝ) {X Y Z Z₀ : Plane}
    (hr : Set.range T.pts = {X, Y, Z}) (hXY : X ≠ Y) (hhXY : h X = h Y) (hZ : h X < h Z)
    (hZ₀ : h X < h Z₀) (d1 : dist X Z = dist X Z₀) (d2 : dist Y Z = dist Y Z₀) :
    Set.range T.pts = {X, Y, Z₀} := by
  rw [hr, third_vertex_unique h hXY hhXY hZ hZ₀ d1 d2]

/-! ## §2 At `P′` in branch (H): the `α`-tile laying `c` on `ℓ⁺` is `T₂ + P′` -/

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- **Identification at `P′`.**  In an `HFrame`, a tile with a corner at `P′` whose flank pair is
`(c·uR, W')`, lying on the band side `{h ≤ h P′}`, and presenting `α` at `P′`, is `T₂ + P′ =
{P′, V + P′ − A, 2P′ − A}`: its other flank has length `b` and the opposite side `a`
(`flank_lengths`, `NearBaseBridge.tile_triple`), and `2P′ − A` is the band-side point at distances
`b = |AP′|` from `P′` and `a = |VP′|` from `P′ + c·uR = V + P′ − A` (`third_vertex_unique`). -/
theorem pprime_alpha_ident (F : HFrame D e f α β γ) {j : Fin N} {m' : Fin 3} {W' : Plane}
    (hm' : (D.tile j).pts m' = F.P)
    (hUW : IsFlankPair (D.tile j) m' F.P (((f : ℝ) ^ 2) • F.uR) W')
    (hband : ∀ q, F.h ((D.tile j).pts q) ≤ F.h F.P)
    (hα : (D.tile j).localAngle F.P = α) : Present D F.T2P := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hef := F.hef
  have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have hc0 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
  have hnc : ‖((f : ℝ) ^ 2) • F.uR‖ = (f : ℝ) ^ 2 := by
    rw [norm_smul, F.huR, mul_one, Real.norm_of_nonneg hc0]
  -- the other flank has length `b`
  have hW : ‖W'‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rcases (flank_lengths F hm' hUW).2.2 hα with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (hnc.symm.trans h1) hbc.symm
    · exact h2
  set Y := F.P + ((f : ℝ) ^ 2) • F.uR with hY
  set Z := F.P + W' with hZ
  have hYV : Y = F.V + F.P - F.A := by rw [hY, F.hV]; abel
  -- the vertices of the tile
  have hverts : ((D.tile j).pts (m' + 1) = Y ∧ (D.tile j).pts (m' + 2) = Z) ∨
      ((D.tile j).pts (m' + 1) = Z ∧ (D.tile j).pts (m' + 2) = Y) := by
    rcases hUW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor
      · rw [hY, h1]; abel
      · rw [hZ, h2]; abel
    · right; constructor
      · rw [hZ, h2]; abel
      · rw [hY, h1]; abel
  have hr : Set.range (D.tile j).pts = {F.P, Y, Z} := by
    ext x; constructor
    · rintro ⟨q, rfl⟩
      rcases fin3_cases3 m' q with rfl | rfl | rfl
      · rw [hm']; simp
      · rcases hverts with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp
      · rcases hverts with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨m', hm'⟩
      · rcases hverts with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact ⟨m' + 1, h1⟩
        · exact ⟨m' + 2, h1⟩
      · rcases hverts with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact ⟨m' + 2, h1⟩
        · exact ⟨m' + 1, h1⟩
  -- distances: `|P′Y| = c`, `|P′Z| = b`, hence `|YZ| = a`
  have dPY : dist F.P Y = (f : ℝ) ^ 2 := by
    rw [hY, dist_comm, dist_eq_norm, add_sub_cancel_left, hnc]
  have dPZ : dist F.P Z = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hZ, dist_comm, dist_eq_norm, add_sub_cancel_left, hW]
  have hP3 := NearBaseBridge.tile_triple (D.tiles_congruent j) F.hM.hs0 F.hM.hs1 F.hM.hs2 m'
  rw [hm'] at hP3
  have dYZ : dist Y Z = (e : ℝ) * f := by
    unfold NearBaseBridge.Perm3 at hP3
    rcases hverts with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hP3 <;>
      rw [dist_comm F.P] at dPY dPZ <;>
      rcases hP3 with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ |
        ⟨k1, k2, k3⟩ <;>
      first
        | exact k3
        | (rw [dist_comm]; exact k3)
        | exact absurd (dPY.symm.trans k1) hac.symm
        | exact absurd (dPY.symm.trans k1) hbc.symm
        | exact absurd (dPZ.symm.trans k1) hab.symm
        | exact absurd (dPZ.symm.trans k1) hbc
        | exact absurd (dPY.symm.trans k2) hac.symm
        | exact absurd (dPY.symm.trans k2) hbc.symm
        | exact absurd (dPZ.symm.trans k2) hab.symm
        | exact absurd (dPZ.symm.trans k2) hbc
  -- `Z` is strictly on the band side (a tile is not flat)
  have hhY : F.h Y = F.h F.P := by
    rw [hY, map_add, map_smul, F.hhuR, smul_zero, add_zero]
  have hZlt : F.h Z < F.h F.P := by
    have hZle : F.h Z ≤ F.h F.P := by
      rcases hverts with ⟨-, h2⟩ | ⟨h2, -⟩
      · rw [← h2]; exact hband _
      · rw [← h2]; exact hband _
    refine lt_of_le_of_ne hZle fun heq => ?_
    apply two_vertices_on_line (D.tile j) F.h (F.h F.P) F.hh0
    intro q
    rcases fin3_cases3 m' q with rfl | rfl | rfl
    · rw [hm']
    · rcases hverts with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> assumption
    · rcases hverts with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> assumption
  -- the candidate `2P′ − A`
  set Z₀ := F.P + F.P - F.A with hZ₀
  have dPZ₀ : dist F.P Z₀ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hZ₀, ← F.hAP, dist_comm F.P, dist_comm F.A, dist_eq_norm, dist_eq_norm]
    congr 1; abel
  have dYZ₀ : dist Y Z₀ = (e : ℝ) * f := by
    rw [hYV, hZ₀, ← F.hVP, dist_eq_norm, dist_eq_norm]
    congr 1; abel
  have hZ₀lt : F.h Z₀ < F.h F.P := by
    rw [hZ₀, map_sub, map_add]; linarith [F.hhP]
  have hPY : F.P ≠ Y := by
    intro h'; rw [← h', dist_self] at dPY; nlinarith
  have hZZ₀ : Z = Z₀ :=
    third_vertex_unique (-F.h) hPY (by simp [hhY]) (by simp [hZlt]) (by simp [hZ₀lt])
      (dPZ.trans dPZ₀.symm) (dYZ.trans dYZ₀.symm)
  refine ⟨j, ?_⟩
  rw [hr, hZZ₀, hYV]
  unfold HFrame.T2P
  rfl

/-- **(iii-b)(I) of `pprime_order`, discharged.**  In (H), the band tile across `K`'s `ℓ⁺`-flank at
`P′` (`pprime_band_tile`, from `CornerAdjacency.flank_neighbour`) lays a band edge `[P′, P′ + Lε·uR]`;
if that edge is a `c`-edge and the tile presents `α` at `P′`, the tile is `T₂ + P′`. -/
theorem pprime_band_alpha_T2P (F : HFrame D e f α β γ) (hK : Present D F.K) :
    ∃ (j : Fin N) (Lε : ℝ), 0 < Lε ∧ (∃ ε ∈ F.band, EdgeIs D ε F.P (F.P + Lε • F.uR)) ∧
      (∃ m' : Fin 3, (D.tile j).pts m' = F.P) ∧
      (Lε = (f : ℝ) ^ 2 → (D.tile j).localAngle F.P = α → Present D F.T2P) := by
  obtain ⟨j, m', W', Lε, hm', hUW, hLpos, hband, hε⟩ := pprime_band_tile F hK
  refine ⟨j, Lε, hLpos, hε, ⟨m', hm'⟩, fun hL hα => ?_⟩
  subst hL
  exact pprime_alpha_ident F hm' hUW hband hα

/-! ## §3 Lemma G, steps 3–4 (`proof_H_empty.md` §5.1): the tile across `T₂`'s `a`-edge is `K` or `M₁`

Generic form, over any `CongruentDissection` whose model has sides `(ef, f² − e², f²)`, coprime
`1 ≤ e < f`.  Inputs, each named: `T₂`'s `a`-edge `[V, P′]` is a tile edge (so `[V, P′]` is a wall);
its open part is interior; a tile contains `V` and has points strictly on both sides of the line
`VP′` (the PIERCER of `thm:pierce(iii)`; with `ThickEFminus1Glue.far_edge_through_V` it is the far
edge of `r` through `V`); no far-side edge on the line passes through `P′` (the two `γ`'s there).
Then (TC-1) the far side of `[V, P′]` is whole edges summing to `a`, which is one `a`-edge
(`Inflation.a_unsplittable`), and (ID) its tile is `K = {V, P′, V + P′ − A}` or the mirror
`{V, P′, M}` of `T₂` across `VP′`. -/

theorem lemmaG {N : ℕ} (D : CongruentDissection N) {e f : ℕ} (hco : Nat.Coprime e f) (he : 1 ≤ e)
    (hef : e < f)
    (hs0 : sideOpp D.model 0 = (e : ℝ) * f) (hs1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp D.model 2 = (f : ℝ) ^ 2)
    (g : Plane →ₗ[ℝ] ℝ) {A V P : Plane} (hgVP : g V = g P) (hgA : g A < g V)
    (hAV : dist A V = (f : ℝ) ^ 2) (hAP : dist A P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hVP : dist V P = (e : ℝ) * f)
    (hT2 : ∃ i k, (D.tile i).edge k = segment ℝ V P)
    (hint : openSegment ℝ V P ⊆ interior D.target.carrier)
    (hpierce : ∃ i, V ∈ (D.tile i).carrier ∧ ∃ p ∈ (D.tile i).carrier, ∃ q ∈ (D.tile i).carrier,
      g p < g V ∧ g V < g q)
    (hPrig : ¬ TraceCovering.Straddled D.toDissection (-g) (-(g V)) P) :
    ∃ j : Fin N, Set.range (D.tile j).pts = {V, P, V + P - A} ∨
      ∃ M : Plane, M ≠ A ∧ dist M V = dist A V ∧ dist M P = dist A P ∧
        Set.range (D.tile j).pts = {V, P, M} := by
  classical
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) < f := by exact_mod_cast hef
  have hab : (e : ℝ) * f ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    intro h
    have hN : e * f + e ^ 2 = f ^ 2 := by
      have : ((e * f + e ^ 2 : ℕ) : ℝ) = ((f ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hdvd : e ∣ f ^ 2 := ⟨f + e, by rw [← hN]; ring⟩
    have he1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hco) hdvd
    subst he1
    have : f * f = f + 1 := by nlinarith
    rcases Nat.lt_or_ge f 2 with h2 | h2
    · interval_cases f <;> omega
    · nlinarith
  have hac : (e : ℝ) * f ≠ (f : ℝ) ^ 2 := by
    intro h; have : (e : ℝ) = f := by
      have h' : (e : ℝ) * f = f * f := by rw [h]; ring
      exact mul_right_cancel₀ (by linarith) h'
    linarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ≠ (f : ℝ) ^ 2 := by intro h; nlinarith
  have hg0 : g ≠ 0 := by intro h; rw [h] at hgA; simp at hgA
  have hg' : (-g : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hg0 (neg_eq_zero.mp h)
  have hgd : ∀ y, (-g) y = -(g V) ↔ g y = g V := TraceCovering.neg_iff
  -- the parametrization of `[V, P′]`
  set d := dist V P with hd
  have hd0 : 0 < d := by rw [hVP]; exact mul_pos (by linarith) (by linarith)
  set u : Plane := d⁻¹ • (P - V) with hu
  have hgu : g u = 0 := by rw [hu, map_smul, map_sub, hgVP, sub_self, smul_zero]
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hd0.le, ← dist_eq_norm, dist_comm, ← hd,
      inv_mul_cancel₀ hd0.ne']
  have hu0 : u ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hPd : V + d • u = P := by rw [hu, smul_smul, mul_inv_cancel₀ hd0.ne', one_smul]; abel
  have hV0 : V + (0 : ℝ) • u = V := by rw [zero_smul, add_zero]
  have hopen : openSegment ℝ V P = (fun x : ℝ => V + x • u) '' Set.Ioo 0 d := by
    have := TraceCovering.openSegment_param (X := V) (u := u) hd0.ne
    rw [hV0, hPd, min_eq_left hd0.le, max_eq_right hd0.le] at this
    exact this
  have hsegVP : segment ℝ V P = (fun x : ℝ => V + x • u) '' Set.Icc 0 d := by
    have := TraceCovering.segment_param (X := V) (u := u) 0 d
    rw [hV0, hPd, min_eq_left hd0.le, max_eq_right hd0.le] at this
    exact this
  have hint' : ∀ x ∈ Set.Ioo 0 d, V + x • u ∈ interior D.target.carrier := fun x hx =>
    hint (hopen ▸ ⟨x, hx, rfl⟩)
  obtain ⟨i2, k2, hk2⟩ := hT2
  have hwall' : ∀ x ∈ Set.Ioo 0 d, ∀ i, V + x • u ∉ interior (D.tile i).carrier := by
    intro x hx
    have hm : V + x • u ∈ (D.tile i2).edge k2 := by
      rw [hk2]; exact openSegment_subset_segment ℝ _ _ (hopen ▸ ⟨x, hx, rfl⟩)
    exact D.toDissection.edge_point_not_interior hm
  -- start condition at `V`: the piercer lies across the line
  have hs : ¬ TraceCovering.Straddled D.toDissection (-g) (-(g V)) (V + (0 : ℝ) • u) := by
    obtain ⟨ip, hVp, p, hp, q, hq, hpg, hqg⟩ := hpierce
    refine TraceCovering.not_straddled_of_near_interior hgd hg0 rfl hgu hu0 ?_
    intro δ hδ
    obtain ⟨x, hx, hxi⟩ := TraceCovering.near_interior_of_across (D.tile ip) hg0 rfl hgu hu0
      (by rw [hV0]; exact hVp) hp hq hpg hqg δ hδ
    exact ⟨x, hx, ip, hxi⟩
  have ht : ¬ TraceCovering.Straddled D.toDissection (-g) (-(g V)) (V + d • u) := by
    rw [hPd]; exact hPrig
  -- TC-1: the far side of `[V, P′]` sums to `a`
  have hsum := TraceCovering.wall_sum (D := D.toDissection) hg' hgd hg0 rfl hgu hu1 hd0.le
    hint' hwall' hs ht
  set sF := (D.toDissection.lineChain (-g) (-(g V))).filter
    (fun e => (D.toDissection.tile e.1).edge e.2 ⊆ segment ℝ (V + (0 : ℝ) • u) (V + d • u))
    with hsF
  obtain ⟨na, nb, nc, hPQR, hcard⟩ := sum_three_values sF
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => edge_len_mem D hs0 hs1 hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  have hnat : na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = e * f := by
    have : ((na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 : ℕ) : ℝ) = ((e * f : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hee]
      rw [hPQR, hsum, hVP]; ring
    exact_mod_cast this
  obtain ⟨hna, hnb, hnc⟩ := Inflation.a_unsplittable e f (f ^ 2 - e ^ 2) na nb nc he hef hco
    (by omega) hnat
  have hcard1 : sF.card = 1 := by omega
  obtain ⟨ε, hε⟩ := Finset.card_eq_one.mp hcard1
  have hεS : ε ∈ sF := by rw [hε]; exact Finset.mem_singleton_self ε
  have hεF := (Finset.mem_filter.mp hεS).1
  have hεin := (Finset.mem_filter.mp hεS).2
  have hdε : dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) = d := by
    have := hsum; rw [hε, Finset.sum_singleton] at this; linarith
  -- the far edge is all of `[V, P′]`
  obtain ⟨h0, h1⟩ := TraceCovering.onLine hgd hεF
  have e0 := TraceCovering.par_spec (TraceCovering.exists_param hg0 rfl hgu hu0 h0)
  have e1 := TraceCovering.par_spec (TraceCovering.exists_param hg0 rfl hgu hu0 h1)
  set s0 := TraceCovering.par V u ((D.tile ε.1).pts ε.2)
  set s1 := TraceCovering.par V u ((D.tile ε.1).pts (ε.2 + 1))
  have hs0m : s0 ∈ Set.Icc 0 d := by
    have hm : (D.tile ε.1).pts ε.2 ∈ segment ℝ V P := by
      rw [hV0, hPd] at hεin; exact hεin (left_mem_segment ℝ _ _)
    rw [hsegVP, e0] at hm
    exact (TraceCovering.lm_injective hu0).mem_set_image.mp hm
  have hs1m : s1 ∈ Set.Icc 0 d := by
    have hm : (D.tile ε.1).pts (ε.2 + 1) ∈ segment ℝ V P := by
      rw [hV0, hPd] at hεin; exact hεin (right_mem_segment ℝ _ _)
    rw [hsegVP, e1] at hm
    exact (TraceCovering.lm_injective hu0).mem_set_image.mp hm
  have hds : max s0 s1 - min s0 s1 = d := by
    rw [← TraceCovering.dist_param (X := V) hu1, ← e0, ← e1, hdε]
  have hends : ((D.tile ε.1).pts ε.2 = V ∧ (D.tile ε.1).pts (ε.2 + 1) = P) ∨
      ((D.tile ε.1).pts ε.2 = P ∧ (D.tile ε.1).pts (ε.2 + 1) = V) := by
    rcases le_total s0 s1 with h | h
    · rw [max_eq_right h, min_eq_left h] at hds
      have hs0z : s0 = 0 := by linarith [hs0m.1, hs1m.2]
      have hs1d : s1 = d := by linarith [hs0m.1, hs1m.2]
      left; exact ⟨by rw [e0, hs0z, hV0], by rw [e1, hs1d, hPd]⟩
    · rw [max_eq_left h, min_eq_right h] at hds
      have hs1z : s1 = 0 := by linarith [hs1m.1, hs0m.2]
      have hs0d : s0 = d := by linarith [hs1m.1, hs0m.2]
      right; exact ⟨by rw [e0, hs0d, hPd], by rw [e1, hs1z, hV0]⟩
  -- the tile `j` of that edge: vertices `V`, `P′`, `Z` with `Z` strictly on the far side
  set j := ε.1
  set Z := (D.tile j).pts (ε.2 + 2) with hZ
  have hr : Set.range (D.tile j).pts = {V, P, Z} := by
    ext x; constructor
    · rintro ⟨q, rfl⟩
      rcases fin3_cases3 ε.2 q with rfl | rfl | rfl
      · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp
      · rcases hends with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp
      · simp [hZ]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rcases hends with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact ⟨ε.2, h1⟩
        · exact ⟨ε.2 + 1, h1⟩
      · rcases hends with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact ⟨ε.2 + 1, h1⟩
        · exact ⟨ε.2, h1⟩
      · exact ⟨ε.2 + 2, rfl⟩
  have hZfar : g V < g Z := by
    have hle : g V ≤ g Z := by
      have := (Dissection.mem_lineChain.mp hεF).2.2 (ε.2 + 2)
      simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
      exact this
    refine lt_of_le_of_ne hle fun heq => ?_
    apply two_vertices_on_line (D.tile j) g (g V) hg0
    intro q
    rcases fin3_cases3 ε.2 q with rfl | rfl | rfl
    · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> exact hgVP.symm
    · rcases hends with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> exact hgVP.symm
    · exact heq.symm
  -- side lengths at `Z`: `{|VZ|, |P′Z|} = {b, c}`
  have hP3 := NearBaseBridge.tile_triple (D.tiles_congruent j) hs0 hs1 hs2 ε.2
  have hVPa : dist V P = (e : ℝ) * f := hVP
  have hcases : (dist V Z = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist P Z = (f : ℝ) ^ 2) ∨
      (dist V Z = (f : ℝ) ^ 2 ∧ dist P Z = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
    unfold NearBaseBridge.Perm3 at hP3
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, ← hZ] at hP3
    · rw [dist_comm P V, dist_comm Z V] at hP3
      rcases hP3 with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ |
        ⟨k1, k2, k3⟩
      · exact Or.inl ⟨k2, k3⟩
      · exact absurd (hVPa.symm.trans k1) hab
      · exact Or.inr ⟨k2, k3⟩
      · exact absurd (hVPa.symm.trans k1) hac
      · exact absurd (hVPa.symm.trans k1) hab
      · exact absurd (hVPa.symm.trans k1) hac
    · rw [dist_comm Z P] at hP3
      rcases hP3 with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ |
        ⟨k1, k2, k3⟩
      · exact Or.inr ⟨k3, k2⟩
      · exact absurd (hVPa.symm.trans k1) hab
      · exact Or.inl ⟨k3, k2⟩
      · exact absurd (hVPa.symm.trans k1) hac
      · exact absurd (hVPa.symm.trans k1) hab
      · exact absurd (hVPa.symm.trans k1) hac
  have hVPne : V ≠ P := by intro h; rw [h, dist_self] at hVPa; nlinarith
  rcases hcases with ⟨hVZ, hPZ⟩ | ⟨hVZ, hPZ⟩
  · -- `γ` at `V`: the half-turn `K = {V, P′, V + P′ − A}`
    refine ⟨j, Or.inl ?_⟩
    have hK0 : g V < g (V + P - A) := by rw [map_sub, map_add, ← hgVP]; linarith
    have dVK : dist V (V + P - A) = dist A P := by
      rw [dist_comm, dist_eq_norm, dist_comm, dist_eq_norm]; congr 1; abel
    have dPK : dist P (V + P - A) = dist A V := by
      rw [dist_comm, dist_eq_norm, dist_comm, dist_eq_norm]; congr 1; abel
    rw [hr, third_vertex_unique g hVPne hgVP hZfar hK0 (by rw [hVZ, dVK, hAP])
      (by rw [hPZ, dPK, hAV])]
  · -- `β` at `V`: the mirror `M₁` of `T₂` across `VP′`
    refine ⟨j, Or.inr ⟨Z, ?_, ?_, ?_, hr⟩⟩
    · intro hZA; rw [hZA] at hZfar; linarith
    · rw [dist_comm, hVZ, hAV]
    · rw [dist_comm, hPZ, hAP]

/-! ## §4 Lemma G in the `HFrame`: the branch split (H)/(M) is a theorem modulo apex placement -/

section Frame

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- `T₂` and `T₃` are distinct tiles presenting `γ` at `P′` (the `K`-free half of
`HFrame.corners_at_pprime`). -/
theorem t2_t3_gamma (F : HFrame D e f α β γ) :
    ∃ i2 i3 : Fin N, i2 ≠ i3 ∧ (D.tile i2).localAngle F.P = γ ∧ (D.tile i3).localAngle F.P = γ := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have hf2 : (0 : ℝ) ≤ (f : ℝ) ^ 2 := by positivity
  have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by rw [F.hV]; exact dist_self_add_unit F.huR hf2
  have hAJ : dist F.A (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 := dist_self_add_unit F.huL hf2
  obtain ⟨i2, h2⟩ := F.hT2
  obtain ⟨i3, h3⟩ := F.hT3
  have h2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3' : Set.range (D.tile i3).pts = {F.P, F.A, F.A + ((f : ℝ) ^ 2) • F.uL} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨i2, i3, ?_, (hloc h2').2.2 hAV, (hloc h3').2.2 hAJ⟩
  intro heq
  subst heq
  have hVmem : F.V ∈ ({F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} : Set Plane) := by
    rw [← h3, h2]; simp
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hfpos : (0 : ℝ) < f := by linarith
  have hepos : (0 : ℝ) < e := by linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hVmem
  rcases hVmem with hVA | hVP | hVJ
  · rw [hVA, dist_self] at hAV; nlinarith
  · have := F.hVP; rw [hVP, dist_self] at this; nlinarith
  · have huRL : F.uR = F.uL := by
      have h' : ((f : ℝ) ^ 2) • F.uR = ((f : ℝ) ^ 2) • F.uL := by
        have := hVJ; rw [F.hV] at this; exact add_left_cancel this
      exact smul_right_injective _ (by positivity : ((f : ℝ) ^ 2) ≠ 0) h'
    have hJ3 : F.A + ((f : ℝ) ^ 3) • F.uL ∈ D.target.carrier := by
      apply subset_convexHull ℝ _
      rw [F.htarget]; simp
    apply F.hrbase ((f : ℝ) * (e : ℝ) ^ 2) (by positivity)
    have : F.A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) + (f : ℝ) * (e : ℝ) ^ 2) • F.uR
        = F.A + ((f : ℝ) ^ 3) • F.uL := by
      rw [huRL]; congr 2; ring
    rw [this]; exact hJ3

/-- **C5 at `P′` without `K`**: every tile containing `P′` has it as a vertex (`γ + γ + π > 2π`). -/
theorem pprime_vertex_of_mem' (F : HFrame D e f α β γ) (i : Fin N)
    (hi : F.P ∈ (D.tile i).carrier) : ∃ m, (D.tile i).pts m = F.P := by
  classical
  by_contra hv
  push Not at hv
  have hang := localAngle_mem_pi_of_mem (D.tile i) hi hv
  obtain ⟨i2, i3, h23, h2, h3⟩ := t2_t3_gamma F
  have hAD := F.hAng
  have hπ := Real.pi_pos
  have hα := hAD.hα
  have hβ := hAD.hβ
  have hγd := hAD.hγdef
  have hrel := hAD.hrel
  have hvals : ∀ i, (D.tile i).localAngle F.P ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem_all D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' F.P i
  have key := VertexFigureReal.interior_multiplicities_cards D.toDissection α β γ hAD.hαβ
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) F.hPint hvals
  set nA := ({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card with hnA
  set nB := ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)).card with hnB
  set nC := ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card with hnC
  set nP := ({i | (D.tile i).localAngle F.P = Real.pi} : Finset (Fin N)).card with hnP
  set nU := ({i | (D.tile i).localAngle F.P = 2 * Real.pi} : Finset (Fin N)).card with hnU
  have h' : ((nA + 3 * nP + 6 * nU : ℕ) : ℝ) * α + ((nB + 2 * nP + 4 * nU : ℕ) : ℝ) * β
      + (nC : ℝ) * (2 * α + β) = ((6 : ℤ) : ℝ) * α + ((4 : ℤ) : ℝ) * β := by
    rw [hγd] at key
    push_cast
    linear_combination key + ((nP : ℝ) + 2 * (nU : ℝ) - 2) * hrel
  obtain ⟨e1, e2⟩ := Geometry.vertex_multiplicities hrel hAD.hirr _ _ _ 6 4 h'
  push_cast at e1 e2
  have hC2 : 2 ≤ nC := by
    have hsub : ({i2, i3} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [h2, h3]
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair h23] at this
  rcases hang with h | h
  · have : 1 ≤ nU := Finset.card_pos.mpr ⟨i, by simp [h]⟩
    omega
  · have : 1 ≤ nP := Finset.card_pos.mpr ⟨i, by simp [h]⟩
    omega

/-- **LEMMA G in the frame** (`proof_H_empty.md` §5.1, all four steps): in an `HFrame` — WITHOUT
assuming branch (H) — the tile across `T₂`'s `a`-edge `VP′` is `K` or the mirror of `T₂` across
`VP′`.  Step 1 = `HFrame.V_pierced` (TC + `e² ∉ S` via Lemma A); step 2 = `pprime_vertex_of_mem'`
(two `γ` at `P′`); steps 3–4 = `lemmaG` (TC + `a` unsplittable + tile identification).  So the
(H)/(M) split is a theorem, conditional only on the frame (apex placement `thm:pierce(i)`, metric
data). -/
theorem lemmaG_frame (F : HFrame D e f α β γ) :
    Present D F.K ∨ ∃ M : Plane, IsMirror F.A F.V F.P M ∧ Present D {F.V, F.P, M} := by
  classical
  have hef := F.hef
  have he := F.he
  have hco := F.hco
  obtain ⟨i2, hi2⟩ := F.hT2
  have hmemT2 : ∀ y ∈ ({F.A, F.V, F.P} : Set Plane), y ∈ (D.tile i2).carrier := by
    intro y hy; rw [← hi2] at hy; obtain ⟨k, rfl⟩ := hy
    exact subset_convexHull ℝ _ ⟨k, rfl⟩
  -- `T₂`'s `a`-edge `[V, P′]`
  obtain ⟨kV, hkV⟩ := MarchInduction.mem_range_of_eq hi2 (show F.V ∈ ({F.A, F.V, F.P} : Set Plane)
    by simp)
  obtain ⟨kP, hkP⟩ := MarchInduction.mem_range_of_eq hi2 (show F.P ∈ ({F.A, F.V, F.P} : Set Plane)
    by simp)
  have hVPne : F.V ≠ F.P := by
    intro h; have := F.hVP; rw [h, dist_self] at this
    have : (0 : ℝ) < (e : ℝ) * f := by
      have : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
      have : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
      positivity
    linarith
  have hkne : kV ≠ kP := by rintro rfl; exact hVPne (hkV.symm.trans hkP)
  obtain ⟨k2, hk2⟩ := (D.tile i2).pair_eq_edge hkne
  rw [hkV, hkP] at hk2
  -- the open edge is interior
  have hVint : F.V ∈ interior D.target.carrier := by
    have hfR : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
    have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
    have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
    have h1 : (f : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
    have h2 : (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
      have := mul_lt_mul_of_pos_left h1 hfR
      nlinarith
    rw [F.hV]
    exact F.hrint _ (by positivity) h2
  have hint : openSegment ℝ F.V F.P ⊆ interior D.target.carrier :=
    D.target.convex.openSegment_closure_interior_subset_interior
      (subset_closure (interior_subset hVint)) F.hPint
  -- the line functional of `VP′`, oriented with `T₂` (`A`) on the negative side
  have hcrA : cross (F.P - F.V) (F.A - F.V) ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := parallel_of_cross_eq_zero (sub_ne_zero.mpr hVPne.symm) h0
    -- then `A − V ∥ P − V`, so `h A = h V + t (h P − h V)`, forcing `h P = h A`
    have hhV : F.h F.V = F.h F.A := by rw [F.hV]; exact TraceCovering.f_param rfl F.hhuR _
    have := congrArg F.h ht
    rw [map_sub, map_smul, map_sub, hhV, sub_self, smul_eq_mul] at this
    have hP := F.hhP
    have ht1 : t ≠ 0 := by
      rintro rfl
      rw [zero_smul, sub_eq_zero] at ht
      exact (Ne.symm hVPne) (by
        exfalso
        have hAP : dist F.A F.P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := F.hAP
        have hAV : F.A = F.V := ht
        have := F.hV; rw [← hAV] at this
        have h2 : ((f : ℝ) ^ 2) • F.uR = 0 := by
          have := congrArg (fun x => x - F.A) this; simpa using this.symm
        rcases smul_eq_zero.mp h2 with h | h
        · have : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
          nlinarith
        · have := F.huR; rw [h, norm_zero] at this; norm_num at this)
    have : t * (F.h F.P - F.h F.A) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact ht1 h
    · linarith
  -- the core, for any orientation `g` with `A` on the negative side
  have core : ∀ g : Plane →ₗ[ℝ] ℝ, g F.V = g F.P → g F.A < g F.V →
      Present D F.K ∨ ∃ M : Plane, IsMirror F.A F.V F.P M ∧ Present D {F.V, F.P, M} := by
    intro g hgVP hgA
    have hg0 : g ≠ 0 := by intro h; rw [h] at hgA; simp at hgA
    -- the piercer at `V`
    have hpierce : ∃ i, F.V ∈ (D.tile i).carrier ∧ ∃ p ∈ (D.tile i).carrier,
        ∃ q ∈ (D.tile i).carrier, g p < g F.V ∧ g F.V < g q := by
      obtain ⟨ε, hε, hVε⟩ := F.V_pierced
      obtain ⟨h0, h1⟩ := TraceCovering.onLine (TraceCovering.neg_iff (f := F.h) (c := F.h F.A)) hε
      have hp0c : (D.tile ε.1).pts ε.2 ∈ (D.tile ε.1).carrier := subset_convexHull ℝ _ ⟨ε.2, rfl⟩
      have hp1c : (D.tile ε.1).pts (ε.2 + 1) ∈ (D.tile ε.1).carrier :=
        subset_convexHull ℝ _ ⟨ε.2 + 1, rfl⟩
      have hVc : F.V ∈ (D.tile ε.1).carrier :=
        (D.tile ε.1).edge_subset_carrier ε.2 (openSegment_subset_segment ℝ _ _ hVε)
      have hp01 : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
        (D.tile ε.1).indep.injective.ne (TraceCovering.fin3_succ_ne ε.2)
      generalize hp0 : (D.tile ε.1).pts ε.2 = p0 at hVε h0 hp0c hp01
      generalize hp1 : (D.tile ε.1).pts (ε.2 + 1) = p1 at hVε h1 hp1c hp01
      have hVne0 : F.V ≠ p0 := by
        intro hc; rw [hc] at hVε; exact hp01 (left_mem_openSegment_iff.mp hVε)
      have hVne1 : F.V ≠ p1 := by
        intro hc; rw [hc] at hVε; exact hp01 (right_mem_openSegment_iff.mp hVε)
      have hhV : F.h F.V = F.h F.A := by rw [F.hV]; exact TraceCovering.f_param rfl F.hhuR _
      obtain ⟨s0, hs0⟩ := TraceCovering.exists_param F.hh0 hhV F.hhuR
        (TraceCovering.ne_zero_of_norm F.huR) h0
      obtain ⟨s1, hs1⟩ := TraceCovering.exists_param F.hh0 hhV F.hhuR
        (TraceCovering.ne_zero_of_norm F.huR) h1
      -- `g uR ≠ 0` (`r` is not parallel to `VP′`)
      have hguR : g F.uR ≠ 0 := by
        intro hgu
        obtain ⟨t, ht⟩ := TraceCovering.exists_param hg0 rfl (show g (F.P - F.V) = 0 by
          rw [map_sub, hgVP, sub_self]) (sub_ne_zero.mpr hVPne.symm)
          (show g (F.V + F.uR) = g F.V by rw [map_add, hgu, add_zero])
        have hu : F.uR = t • (F.P - F.V) := add_left_cancel ht
        have := congrArg F.h hu
        rw [F.hhuR, map_smul, map_sub, hhV, smul_eq_mul] at this
        have hP := F.hhP
        rcases mul_eq_zero.mp this.symm with h | h
        · rw [h, zero_smul] at hu
          have := F.huR; rw [hu, norm_zero] at this; norm_num at this
        · linarith
      have hs0ne : s0 ≠ 0 := by rintro rfl; apply hVne0; rw [hs0, zero_smul, add_zero]
      have hs1ne : s1 ≠ 0 := by rintro rfl; apply hVne1; rw [hs1, zero_smul, add_zero]
      obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hVε
      have hg0' : g p0 = g F.V + s0 * g F.uR := by rw [hs0, map_add, map_smul, smul_eq_mul]
      have hg1' : g p1 = g F.V + s1 * g F.uR := by rw [hs1, map_add, map_smul, smul_eq_mul]
      have hlin : a * (s0 * g F.uR) + b * (s1 * g F.uR) = 0 := by
        have := congrArg g hcomb
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hg0', hg1'] at this
        have h2 : (a + b) * g F.V + (a * (s0 * g F.uR) + b * (s1 * g F.uR)) = g F.V := by
          linarith
        rw [hab, one_mul] at h2; linarith
      have hne0 : s0 * g F.uR ≠ 0 := mul_ne_zero hs0ne hguR
      rcases lt_or_gt_of_ne hne0 with hneg | hpos
      · have : 0 < s1 * g F.uR := by
          by_contra hc; push Not at hc
          have h3 : a * (s0 * g F.uR) < 0 := mul_neg_of_pos_of_neg ha hneg
          have h4 : b * (s1 * g F.uR) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hc
          linarith
        exact ⟨ε.1, hVc, p0, hp0c, p1, hp1c, by linarith, by linarith⟩
      · have : s1 * g F.uR < 0 := by
          by_contra hc; push Not at hc
          have h3 : 0 < a * (s0 * g F.uR) := mul_pos ha hpos
          have h4 : 0 ≤ b * (s1 * g F.uR) := mul_nonneg hb.le hc
          linarith
        exact ⟨ε.1, hVc, p1, hp1c, p0, hp0c, by linarith, by linarith⟩
    -- no far edge through `P′`
    have hPrig : ¬ TraceCovering.Straddled D.toDissection (-g) (-(g F.V)) F.P := by
      rintro ⟨ε, -, hPε⟩
      have hp01 : (D.tile ε.1).pts ε.2 ≠ (D.tile ε.1).pts (ε.2 + 1) :=
        (D.tile ε.1).indep.injective.ne (TraceCovering.fin3_succ_ne ε.2)
      have hPe : F.P ∈ (D.tile ε.1).edge ε.2 := openSegment_subset_segment ℝ _ _ hPε
      obtain ⟨m, hm⟩ := pprime_vertex_of_mem' F ε.1 ((D.tile ε.1).edge_subset_carrier ε.2 hPe)
      have hne0 : F.P ≠ (D.tile ε.1).pts ε.2 := by
        intro hc; rw [hc] at hPε; exact hp01 (left_mem_openSegment_iff.mp hPε)
      have hne1 : F.P ≠ (D.tile ε.1).pts (ε.2 + 1) := by
        intro hc; rw [hc] at hPε; exact hp01 (right_mem_openSegment_iff.mp hPε)
      rcases fin3_cases3 ε.2 m with rfl | rfl | rfl
      · exact hne0 hm.symm
      · exact hne1 hm.symm
      · have hz := (D.tile ε.1).coord_eq_zero_of_mem_edge ε.2 hPe
        rw [← hm, show (D.tile ε.1).pts (ε.2 + 2) = (D.tile ε.1).basis (ε.2 + 2) from rfl,
          AffineBasis.coord_apply_eq] at hz
        exact one_ne_zero hz
    have hAV' : dist F.A F.V = (f : ℝ) ^ 2 := by
      rw [F.hV]; exact dist_self_add_unit F.huR (by positivity)
    obtain ⟨j, hj⟩ := lemmaG D hco (by omega) (by omega) F.hM.hs0 F.hM.hs1 F.hM.hs2 g hgVP hgA
      hAV' F.hAP F.hVP ⟨i2, k2, hk2.symm⟩ hint hpierce hPrig
    rcases hj with hK | ⟨M, hMA, hMV, hMP, hM⟩
    · left; exact ⟨j, by rw [hK]; unfold HFrame.K; rfl⟩
    · right; exact ⟨M, ⟨hMA, hMV, hMP⟩, j, hM⟩
  -- choose the orientation
  rcases lt_or_gt_of_ne hcrA with hneg | hpos
  · refine core (crossL (F.P - F.V)) ?_ ?_
    · show cross (F.P - F.V) F.V = cross (F.P - F.V) F.P
      have : cross (F.P - F.V) (F.P - F.V) = 0 := by simp [cross]; ring
      rw [cross_sub_right] at this; linarith
    · show cross (F.P - F.V) F.A < cross (F.P - F.V) F.V
      rw [cross_sub_right] at hneg; linarith
  · refine core (-crossL (F.P - F.V)) ?_ ?_
    · show -cross (F.P - F.V) F.V = -cross (F.P - F.V) F.P
      have : cross (F.P - F.V) (F.P - F.V) = 0 := by simp [cross]; ring
      rw [cross_sub_right] at this; linarith
    · show -cross (F.P - F.V) F.A < -cross (F.P - F.V) F.V
      rw [cross_sub_right] at hpos; linarith

end Frame

end Erdos634.Draft.TileIdent

#print axioms Erdos634.Draft.TileIdent.third_vertex_unique
#print axioms Erdos634.Draft.TileIdent.tile_ident
#print axioms Erdos634.Draft.TileIdent.pprime_alpha_ident
#print axioms Erdos634.Draft.TileIdent.pprime_band_alpha_T2P
#print axioms Erdos634.Draft.TileIdent.lemmaG
#print axioms Erdos634.Draft.TileIdent.t2_t3_gamma
#print axioms Erdos634.Draft.TileIdent.pprime_vertex_of_mem'
#print axioms Erdos634.Draft.TileIdent.lemmaG_frame
