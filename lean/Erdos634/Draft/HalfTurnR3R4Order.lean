-- Draft/HalfTurnR3R4Order.lean — the corner-order half of R4 S1 (`pprime_order`) at P′, PROVED.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- `HalfTurnR3R4Glue.pprime_order` (sorry) asserts: in (H), the first band-side edge on ℓ⁺ from P′
-- has length `b` or `c`, never `a`, and if `c` its tile is `T₂ + P′`.  Its prose proof (proof_R4.md
-- Step 1) has three parts: (i) every tile at P′ has P′ as a vertex (C5, angle count); (ii) the corner
-- order at P′: some band-side tile has a corner at P′ with a flank along ℓ⁺ (the tile across K's
-- ℓ⁺-flank); (iii) the residual-γ bookkeeping (Z across P′J₁ lays exactly `a` — trace covering —
-- then `{γ}` or `{β, α, α}`) that excludes `a` and identifies `T₂ + P′`.
--
-- PROVED here (no `sorry`):
--   * `localAngle_mem_pi_of_mem` — a tile containing `p` but not having it as a vertex has local
--     angle `π` or `2π` there.
--   * `pprime_vertex_of_mem` — (i): every tile containing P′ has P′ as a vertex (`T₂`, `T₃` give
--     `γ, γ`, `K` gives `β` — `corners_at_pprime`, now PROVED — and `2γ + β + π > 2π` by the integer
--     multiplicity bridge).
--   * `pprime_band_edge` — (ii): there IS a band-side edge on ℓ⁺ starting at P′, of length
--     `Lε ∈ {a, b, c}`, belonging to a tile with a corner at P′ — the tile across `K`'s ℓ⁺-flank
--     (`CornerAdjacency.flank_neighbour_dissection`), on the band side `{h < h P′}`.
--   * `pprime_figure_cases` — the residual at P′ is `{γ}` or `{β, α, α}` (counting only).
--   * `J1_not_interior`, `pprime_across_J1` — at `a < b` (`e² + ef < f²`): the tile across `T₃`'s
--     `a`-edge P′J₁ lays EXACTLY the whole `a`-edge `[P′, J₁]` (R4 (a), first clause; a longer flank
--     would make the leg point `J₁` interior — no trace covering needed).
--   * `V_ne_J1`, `J1_not_along_uR`, `flank_mem`, `flank_lengths`, `pprime_band_tile` — plumbing.
--   * `pprime_band_edge_not_a` — at `a < b`: the first band edge on ℓ⁺ from P′ is `b` or `c`, NEVER
--     `a` (R4 (a), second clause) = `pprime_order` minus its `T₂ + P′` clause, at these members.
-- NOT proved: `pprime_order`'s clause `Lε = c → T₂ + P′` (any member), and `Lε ≠ a` at `b < a`.
-- See the reduction at the foot.
--
-- Build (scratch oleans; never .lake):
--   lake env lean -o $S/Erdos634/Draft/HalfTurnR3R4.olean Erdos634/Draft/HalfTurnR3R4.lean
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean -o $S/Erdos634/Draft/HalfTurnR3R4Glue.olean Erdos634/Draft/HalfTurnR3R4Glue.lean'
--   (NearBaseVertex, NearBase, NearBaseKill, NearBaseBridge, CornerAdjacency oleans likewise)
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/HalfTurnR3R4Order.lean'
import Erdos634.Draft.HalfTurnR3R4Glue
import Erdos634.Draft.CornerAdjacency
import Erdos634.Draft.NearBaseBridge

namespace Erdos634.Draft.HalfTurnR3R4Order

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency

/-- A tile containing `p`, without `p` as a vertex, has local angle `2π` or `π` at `p`. -/
theorem localAngle_mem_pi_of_mem (T : Tri) {p : Plane} (hp : p ∈ T.carrier)
    (hv : ∀ m, T.pts m ≠ p) : T.localAngle p = 2 * Real.pi ∨ T.localAngle p = Real.pi := by
  classical
  have hnv : ¬ ∃ j, p = T.pts j := by rintro ⟨j, hj⟩; exact hv j hj.symm
  rcases T.classify (fun k h => hv k h.symm) with hall | ⟨m, hm0, hmpos⟩ | ⟨m, hneg⟩
  · left; rw [Tri.localAngle, dif_neg hnv, if_pos hall]
  · right
    have hnall : ¬ ∀ j, 0 < T.basis.coord j p := fun h => by have := h m; linarith
    rw [Tri.localAngle, dif_neg hnv, if_neg hnall, if_pos ⟨m, hm0, hmpos⟩]
  · exfalso
    have := ((NearBaseVertex.mem_carrier_iff T p).mp hp) m
    linarith

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- **(i) Every tile containing P′ has P′ as a vertex** (C5 at P′).  The figure at P′ contains
`γ, γ` (`T₂`, `T₃`) and `β` (`K`) — `HFrame.corners_at_pprime`, PROVED — so a straight (`π`) or full
(`2π`) contribution would overfill `2π` (integer multiplicities: `n_β + n_γ + 2n_π + 4n_{2π} = 4`). -/
theorem pprime_vertex_of_mem (F : HFrame D e f α β γ) (hK : Present D F.K) (i : Fin N)
    (hi : F.P ∈ (D.tile i).carrier) : ∃ m, (D.tile i).pts m = F.P := by
  classical
  by_contra hv
  push Not at hv
  have hang := localAngle_mem_pi_of_mem (D.tile i) hi hv
  obtain ⟨i2, i3, k, h23, h2, h3, hk⟩ := F.corners_at_pprime hK
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
  have hB1 : 1 ≤ nB := Finset.card_pos.mpr ⟨k, by simp [hk]⟩
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

/-- **The figure at P′ in (H), by counting alone** (no corner order): with `T₂, T₃` (`γ, γ`) and `K`
(`β`) present, the multiplicities at P′ are `(n_α, n_β, n_γ) = (0, 1, 3)` or `(2, 2, 2)`, with no
straight or full angle; i.e. the residual `γ` is filled by `{γ}` or by `{β, α, α}` (proof_R4.md
Step 1).  With `t2pprime_forced` (an `α` present) only `(2,2,2)` survives (`r4_figure_at_pprime`). -/
theorem pprime_figure_cases (F : HFrame D e f α β γ) (hK : Present D F.K) :
    ({i | (D.tile i).localAngle F.P = Real.pi} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle F.P = 2 * Real.pi} : Finset (Fin N)).card = 0 ∧
    ((({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card = 0 ∧
      ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)).card = 1 ∧
      ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card = 3) ∨
     (({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card = 2)) := by
  classical
  obtain ⟨i2, i3, k, h23, h2, h3, hk⟩ := F.corners_at_pprime hK
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
  have hB1 : 1 ≤ nB := Finset.card_pos.mpr ⟨k, by simp [hk]⟩
  have hC2 : 2 ≤ nC := by
    have hsub : ({i2, i3} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [h2, h3]
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair h23] at this
  refine ⟨by omega, by omega, ?_⟩
  rcases Nat.lt_or_ge nC 3 with h | h
  · right; omega
  · left; omega

theorem fin3_add_two_add_one (m : Fin 3) : m + 2 + 1 = m := by fin_cases m <;> decide

theorem fin3_cases3 (m i : Fin 3) : i = m ∨ i = m + 1 ∨ i = m + 2 := by
  fin_cases m <;> fin_cases i <;> decide

/-- `h` vanishes on `uR`, so it is proportional to `cross(uR, ·)`:
`cross(uR, n)·h(v) = cross(uR, v)·h(n)`. -/
theorem h_prop (F : HFrame D e f α β γ) (v n : Plane) :
    cross F.uR n * F.h v = cross F.uR v * F.h n := by
  have hc := cramer F.uR n v
  have := congrArg F.h hc
  rw [map_smul, map_add, map_smul, map_smul, F.hhuR, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_zero, zero_add] at this
  exact this

/-- **(ii) The first band edge on ℓ⁺ at P′ exists (corner order at P′).**  In (H) (`K` present),
some tile with a corner at P′ lays an edge `[P′, P′ + Lε·uR]` on ℓ⁺, lies on the band side
`{h ≤ h P′}` (so the edge is in `F.band`), and `Lε ∈ {a, b, c}`.  It is the tile across `K`'s
ℓ⁺-flank `P′Q₁` (`flank_neighbour_dissection`); the edge case there is excluded by
`pprime_vertex_of_mem`. -/
theorem pprime_band_edge (F : HFrame D e f α β γ) (hK : Present D F.K) :
    ∃ ε ∈ F.band, ∃ Lε : ℝ,
      (Lε = (e : ℝ) * f ∨ Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ Lε = (f : ℝ) ^ 2) ∧
      EdgeIs D ε F.P (F.P + Lε • F.uR) ∧ ∃ m, (D.tile ε.1).pts m = F.P := by
  classical
  have hK' := hK
  obtain ⟨k, hk⟩ := hK
  set Q1 := F.V + F.P - F.A with hQ1
  have hkr : Set.range (D.tile k).pts = {F.P, Q1, F.V} := by
    rw [hk]; unfold HFrame.K; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨m, hm⟩ := Erdos634.MarchInduction.mem_range_of_eq hkr (Set.mem_insert _ _)
  have hflank : IsFlankPair (D.tile k) m F.P (Q1 - F.P) (F.V - F.P) := by
    rcases Erdos634.MarchInduction.vertex_data_of_range hkr hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  obtain ⟨j, -, hPj, hcase⟩ := flank_neighbour_dissection D.toDissection F.hPint hm hflank
  rcases hcase with ⟨m', hm', U', W', hUW', S, hS, hQU, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m'', hm''⟩ := pprime_vertex_of_mem F hK' j hPj
    exact NearBaseVertex.vertex_not_edge (D.tile j) m'' hm'' m' hmpos
  -- `Q₁ − P′ = c·uR`
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by
    have := F.hef; have : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
    positivity
  have hQ : Q1 - F.P = ((f : ℝ) ^ 2) • F.uR := by
    have : Q1 - F.P = F.V - F.A := by rw [hQ1]; abel
    rw [this, F.hV, add_sub_cancel_left]
  set Lε := (f : ℝ) ^ 2 / S with hLε
  have hLpos : 0 < Lε := by positivity
  have hU' : U' = Lε • F.uR := by
    have h1 : S • U' = ((f : ℝ) ^ 2) • F.uR := by rw [← hQU, hQ]
    have h2 : U' = S⁻¹ • (S • U') := by rw [smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
    rw [h2, h1, smul_smul, hLε, div_eq_inv_mul]
  have hnU' : ‖U'‖ = Lε := by
    rw [hU', norm_smul, F.huR, mul_one, Real.norm_of_nonneg hLpos.le]
  -- the side: `h(W') < 0`
  have hVP : 0 < F.h (F.V - F.P) := by
    have hhV : F.h F.V = F.h F.A := by
      rw [F.hV, map_add, map_smul, F.hhuR, smul_zero, add_zero]
    rw [map_sub, hhV]; linarith [F.hhP]
  have hW' : F.h W' < 0 := by
    have hs2 : cross F.uR W' * cross F.uR (F.V - F.P) < 0 := by
      rw [hQ, cross_smul_left', cross_smul_left'] at hside
      have e3 : (f : ℝ) ^ 2 * cross F.uR W' * ((f : ℝ) ^ 2 * cross F.uR (F.V - F.P))
          = ((f : ℝ) ^ 2 * (f : ℝ) ^ 2) * (cross F.uR W' * cross F.uR (F.V - F.P)) := by ring
      rw [e3] at hside
      by_contra hc; push Not at hc
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ (f : ℝ) ^ 2 * (f : ℝ) ^ 2) hc
      linarith
    have hp := h_prop F W' (F.V - F.P)
    by_contra hc; push Not at hc
    have : 0 ≤ cross F.uR (F.V - F.P) ^ 2 * F.h W' := by positivity
    have e4 : cross F.uR (F.V - F.P) ^ 2 * F.h W'
        = cross F.uR (F.V - F.P) * (cross F.uR W' * F.h (F.V - F.P)) := by rw [← hp]; ring
    rw [e4] at this
    have : cross F.uR W' * cross F.uR (F.V - F.P) * F.h (F.V - F.P) < 0 :=
      mul_neg_of_neg_of_pos hs2 hVP
    nlinarith
  -- the vertices of tile `j`
  have hhU : F.h (F.P + U') = F.h F.P := by
    rw [map_add, hU', map_smul, F.hhuR, smul_zero, add_zero]
  have hhW : F.h (F.P + W') < F.h F.P := by rw [map_add]; linarith
  have hdist : dist (F.P + U') F.P = Lε := by
    rw [dist_eq_norm, add_sub_cancel_left, hnU']
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hmem : ∀ q : Fin 3, q ≠ m' → (D.tile j).pts q = F.P + U' →
      (Lε = (e : ℝ) * f ∨ Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ Lε = (f : ℝ) ^ 2) := by
    intro q hq hqU
    have := NearBaseBridge.tile_dist_mem (D.tiles_congruent j) F.hM.hs0 F.hM.hs1 F.hM.hs2 q m' hq
    rw [hqU, hm', hdist] at this
    exact this
  have hband : ∀ q : Fin 3, F.h ((D.tile j).pts q) ≤ F.h F.P := by
    intro q
    rcases fin3_cases3 m' q with rfl | rfl | rfl
    · rw [hm']
    · rcases hUW' with ⟨h1, -⟩ | ⟨-, h2⟩
      · have : (D.tile j).pts (m' + 1) = F.P + U' := by rw [h1]; abel
        rw [this, hhU]
      · have : (D.tile j).pts (m' + 1) = F.P + W' := by rw [h2]; abel
        rw [this]; exact hhW.le
    · rcases hUW' with ⟨-, h2⟩ | ⟨h1, -⟩
      · have : (D.tile j).pts (m' + 2) = F.P + W' := by rw [h2]; abel
        rw [this]; exact hhW.le
      · have : (D.tile j).pts (m' + 2) = F.P + U' := by rw [h1]; abel
        rw [this, hhU]
  rcases hUW' with ⟨h1, -⟩ | ⟨h1, -⟩
  · -- the edge `(j, m')`
    have hq : (D.tile j).pts (m' + 1) = F.P + U' := by rw [h1]; abel
    refine ⟨(j, m'), ?_, Lε, hmem (m' + 1) (NearBaseVertex.succ_ne' m') hq, ?_, m', hm'⟩
    · show (j, m') ∈ D.toDissection.lineChain F.h (F.h F.P)
      rw [Dissection.mem_lineChain]
      refine ⟨by simp only [hm'], by simp only; rw [hq, hhU], fun q => hband q⟩
    · show ({(D.tile j).pts m', (D.tile j).pts (m' + 1)} : Set Plane) = {F.P, F.P + Lε • F.uR}
      rw [hm', hq, hU']
  · -- the edge `(j, m' + 2)`
    have hq : (D.tile j).pts (m' + 2) = F.P + U' := by rw [h1]; abel
    refine ⟨(j, m' + 2), ?_, Lε, hmem (m' + 2) (NearBaseVertex.succ_succ_ne' m') hq, ?_, m', hm'⟩
    · show (j, m' + 2) ∈ D.toDissection.lineChain F.h (F.h F.P)
      rw [Dissection.mem_lineChain]
      refine ⟨by simp only; rw [hq, hhU], by simp only; rw [fin3_add_two_add_one, hm'],
        fun q => hband q⟩
    · show ({(D.tile j).pts (m' + 2), (D.tile j).pts (m' + 2 + 1)} : Set Plane)
        = {F.P, F.P + Lε • F.uR}
      rw [fin3_add_two_add_one, hm', hq, hU', Set.pair_comm]

/-! ## (T) at `a < b`: the tile across P′J₁ lays exactly `a` (no trace covering needed) -/

/-- `J₁ = A + c·uL` lies on the leg `[A, A + f³·uL]` (an edge of the target), so it is not interior. -/
theorem J1_not_interior (F : HFrame D e f α β γ) :
    F.A + ((f : ℝ) ^ 2) • F.uL ∉ interior D.target.carrier := by
  intro hJ
  have hpos := (Tri.mem_interior_iff_coord_pos _ _).mp hJ
  have hef := F.hef
  have hf : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
  set L := F.A + ((f : ℝ) ^ 3) • F.uL with hL
  obtain ⟨iA, hiA⟩ := Erdos634.MarchInduction.mem_range_of_eq F.htarget
    (by simp : F.A ∈ ({F.A, L, F.R} : Set Plane))
  obtain ⟨iL, hiL⟩ := Erdos634.MarchInduction.mem_range_of_eq F.htarget
    (by simp : L ∈ ({F.A, L, F.R} : Set Plane))
  obtain ⟨iR, hiR⟩ := Erdos634.MarchInduction.mem_range_of_eq F.htarget
    (by simp : F.R ∈ ({F.A, L, F.R} : Set Plane))
  have hinj := D.target.indep.injective
  have hRA : F.R ≠ F.A := by
    intro h; have := F.hlegR; rw [h, dist_self] at this
    have : (0 : ℝ) < (f : ℝ) ^ 3 := by positivity
    linarith
  have hiRA : iR ≠ iA := fun h => hRA (by rw [← hiR, ← hiA, h])
  have hiRL : iR ≠ iL := by
    intro h
    have hq : ∀ q, D.target.pts q = F.A ∨ D.target.pts q = L := by
      intro q
      have : D.target.pts q ∈ ({F.A, L, F.R} : Set Plane) := F.htarget ▸ ⟨q, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · right; rw [h1, ← hiR, h, hiL]
    rcases hq 0 with h0 | h0 <;> rcases hq 1 with h1 | h1 <;> rcases hq 2 with h2 | h2
    all_goals first
      | exact absurd (hinj (h0.trans h1.symm)) (by decide)
      | exact absurd (hinj (h0.trans h2.symm)) (by decide)
      | exact absurd (hinj (h1.trans h2.symm)) (by decide)
  have hline : F.A + ((f : ℝ) ^ 2) • F.uL = AffineMap.lineMap F.A L (1 / (f : ℝ)) := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hL, add_sub_cancel_left, smul_smul]
    rw [show 1 / (f : ℝ) * (f : ℝ) ^ 3 = (f : ℝ) ^ 2 by field_simp]
    abel
  have h0 := hpos iR
  rw [hline, AffineMap.apply_lineMap, ← hiA, ← hiL, NearBaseVertex.coord_other _ hiRA,
    NearBaseVertex.coord_other _ hiRL, AffineMap.lineMap_same_apply] at h0
  exact lt_irrefl _ h0

/-- **R4 (a), first clause, at `a < b` (`e² + ef < f²`): the tile across `T₃`'s `a`-edge P′J₁ lays
exactly the whole `a`-edge `[P′, J₁]`.**  `flank_neighbour` gives a tile `Z ≠ T₃` with a corner at P′
and a flank positively along `J₁ − P′`, its other flank across the line P′J₁ from `A`; the flank has
length `a`, `b` or `c`; a flank longer than `a` would put its endpoint beyond `J₁` in the target, making
the leg point `J₁` interior (`J1_not_interior`); at `a < b` only `a` remains.  (At `b < a` a `b`-flank
is not excluded by this argument: that case still needs trace covering of `[P′, J₁]`.) -/
theorem pprime_across_J1 (F : HFrame D e f α β γ) (hK : Present D F.K)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2) :
    ∃ i3 z : Fin N, Set.range (D.tile i3).pts = {F.A, F.P, F.A + ((f : ℝ) ^ 2) • F.uL} ∧
      z ≠ i3 ∧ ∃ (mz : Fin 3) (W'' : Plane), (D.tile z).pts mz = F.P ∧
        IsFlankPair (D.tile z) mz F.P (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) W'' ∧
        cross (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) W''
          * cross (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) (F.A - F.P) < 0 := by
  classical
  set J1 := F.A + ((f : ℝ) ^ 2) • F.uL with hJ1
  obtain ⟨i3, h3⟩ := F.hT3
  have h3r : Set.range (D.tile i3).pts = {F.P, J1, F.A} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨m3, hm3⟩ := Erdos634.MarchInduction.mem_range_of_eq h3r (Set.mem_insert _ _)
  have hflank : IsFlankPair (D.tile i3) m3 F.P (J1 - F.P) (F.A - F.P) := by
    rcases Erdos634.MarchInduction.vertex_data_of_range h3r hm3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  obtain ⟨z, hz3, hPz, hcase⟩ := flank_neighbour_dissection D.toDissection F.hPint hm3 hflank
  refine ⟨i3, z, h3, hz3, ?_⟩
  rcases hcase with ⟨mz, hmz, U'', W'', hUW, S, hS, hJU, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m'', hm''⟩ := pprime_vertex_of_mem F hK z hPz
    exact NearBaseVertex.vertex_not_edge (D.tile z) m'' hm'' m' hmpos
  obtain ⟨q, hq, hqU⟩ : ∃ q, q ≠ mz ∧ (D.tile z).pts q = F.P + U'' := by
    rcases hUW with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨mz + 1, NearBaseVertex.succ_ne' mz, by rw [h1]; abel⟩
    · exact ⟨mz + 2, NearBaseVertex.succ_succ_ne' mz, by rw [h1]; abel⟩
  have hlen := NearBaseBridge.tile_dist_mem (D.tiles_congruent z) F.hM.hs0 F.hM.hs1 F.hM.hs2
    q mz hq
  rw [hqU, hmz, dist_eq_norm, add_sub_cancel_left] at hlen
  have hJP : ‖J1 - F.P‖ = (e : ℝ) * f := by rw [← dist_eq_norm, dist_comm]; exact F.hPJ1
  have hSU : S * ‖U''‖ = (e : ℝ) * f := by
    rw [← hJP, hJU, norm_smul, Real.norm_of_nonneg hS.le]
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  -- a flank longer than `a` makes `J₁` interior
  have hle : ‖U''‖ ≤ (e : ℝ) * f := by
    by_contra hgt; push Not at hgt
    have hS1 : S < 1 := by
      by_contra h1; push Not at h1
      have : (e : ℝ) * f < S * ‖U''‖ := by nlinarith
      linarith
    apply J1_not_interior F
    have hE : F.P + U'' ∈ D.target.carrier := by
      rw [← hqU]; exact Erdos634.MarchInduction.pts_mem_target D.toDissection z q
    refine (D.target.convex.openSegment_interior_closure_subset_interior F.hPint
      (subset_closure hE)) ⟨1 - S, S, by linarith, hS, by ring, ?_⟩
    have : F.A + ((f : ℝ) ^ 2) • F.uL = F.P + S • U'' := by rw [← hJ1, ← hJU]; abel
    rw [this]; module
  have hUa : ‖U''‖ = (e : ℝ) * f := by
    rcases hlen with h | h | h
    · exact h
    · linarith
    · linarith
  have hS1 : S = 1 := by
    have : S * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by
      calc S * ((e : ℝ) * f) = S * ‖U''‖ := by rw [hUa]
        _ = (e : ℝ) * f := hSU
        _ = 1 * ((e : ℝ) * f) := (one_mul _).symm
    exact mul_right_cancel₀ ha0.ne' this
  have hU : U'' = J1 - F.P := by rw [hJU, hS1, one_smul]
  refine ⟨mz, W'', hmz, ?_, hside⟩
  rw [← hU]; exact hUW

/-! ## "Never `a`" at `a < b`: the first band edge on ℓ⁺ from P′ is `b` or `c` -/

theorem V_ne_J1 (F : HFrame D e f α β γ) : F.V ≠ F.A + ((f : ℝ) ^ 2) • F.uL := by
  intro hVJ
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have hfpos : (0 : ℝ) < f := by linarith
  have huRL : F.uR = F.uL := by
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

/-- `J₁ − P′` is not along `uR`: `J₁ = P′ + s·uR` with the frame's distances forces
`e f (e−f)²(e+f)(e+2f) = 0`. -/
theorem J1_not_along_uR (F : HFrame D e f α β γ) {s : ℝ} (hs : 0 < s) :
    F.A + ((f : ℝ) ^ 2) • F.uL - F.P ≠ s • F.uR := by
  intro hJ
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  set a := (e : ℝ) * f
  set b := (f : ℝ) ^ 2 - (e : ℝ) ^ 2
  set c := (f : ℝ) ^ 2
  set w := F.P - F.A with hw
  have hnw : ‖w‖ = b := by rw [hw, ← dist_eq_norm, dist_comm]; exact F.hAP
  have hsa : s = a := by
    have h1 : ‖F.A + c • F.uL - F.P‖ = a := by rw [← dist_eq_norm, dist_comm]; exact F.hPJ1
    rw [hJ, norm_smul, F.huR, mul_one, Real.norm_of_nonneg hs.le] at h1; exact h1
  -- `‖a·uR + w‖ = c` and `‖c·uR − w‖ = a`
  have h1 : ‖s • F.uR + w‖ = c := by
    have : s • F.uR + w = c • F.uL := by rw [← hJ, hw]; abel
    rw [this, norm_smul, F.huL, mul_one, Real.norm_of_nonneg (by positivity)]
  have h2 : ‖c • F.uR - w‖ = a := by
    have : c • F.uR - w = F.V - F.P := by rw [F.hV, hw]; abel
    rw [this, ← dist_eq_norm]; exact F.hVP
  set t := inner ℝ F.uR w with ht
  have hu2 : ‖F.uR‖ ^ 2 = 1 := by rw [F.huR]; norm_num
  have e1 : ‖s • F.uR + w‖ ^ 2 = s ^ 2 + 2 * s * t + b ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_left, norm_smul, mul_pow, hu2, hnw,
      Real.norm_of_nonneg hs.le]; ring
  have e2 : ‖c • F.uR - w‖ ^ 2 = c ^ 2 - 2 * c * t + b ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_left, norm_smul, mul_pow, hu2, hnw,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ c)]; ring
  rw [h1] at e1; rw [h2] at e2; rw [hsa] at e1
  have key : (e : ℝ) * f * ((e : ℝ) - f) ^ 2 * ((e : ℝ) + f) * ((e : ℝ) + 2 * f) = 0 := by
    simp only [a, b, c] at e1 e2
    linear_combination (-(f : ℝ) ^ 2) * e1 + (-((e : ℝ) * f)) * e2
  have hpos : 0 < (e : ℝ) * f * ((e : ℝ) - f) ^ 2 * ((e : ℝ) + f) * ((e : ℝ) + 2 * f) := by
    have : (0 : ℝ) < ((e : ℝ) - f) ^ 2 := by
      have : (e : ℝ) - f ≠ 0 := by intro h; linarith
      positivity
    have h0 : (0 : ℝ) < e := by linarith
    have h0' : (0 : ℝ) < f := by linarith
    positivity
  linarith

/-- The two flank pairs at one corner share their members. -/
theorem flank_mem {T : Tri} {m : Fin 3} {x U W U' W' : Plane} (h : IsFlankPair T m x U W)
    (h' : IsFlankPair T m x U' W') : (U' = U ∧ W' = W) ∨ (U' = W ∧ W' = U) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · left; exact ⟨h3.trans h1.symm, h4.trans h2.symm⟩
  · right; exact ⟨h3.trans h2.symm, h4.trans h1.symm⟩
  · right; exact ⟨h3.trans h2.symm, h4.trans h1.symm⟩
  · left; exact ⟨h3.trans h1.symm, h4.trans h2.symm⟩

/-- Flank lengths of a tile at a corner of given angle: `γ ↦ {a,b}`, `β ↦ {a,c}`, `α ↦ {b,c}`. -/
theorem flank_lengths (F : HFrame D e f α β γ) {i : Fin N} {m : Fin 3} {U W : Plane}
    (hm : (D.tile i).pts m = F.P) (hUW : IsFlankPair (D.tile i) m F.P U W) :
    ((D.tile i).localAngle F.P = γ →
      (‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
      (‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
    ((D.tile i).localAngle F.P = β →
      (‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2) ∨ (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
    ((D.tile i).localAngle F.P = α →
      (‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2) ∨
      (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) F.hM.hs0 F.hM.hs1 F.hM.hs2 m
  have hL := localAngle_of_oppSideE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ'
    F.hM.hγ' i m
  rw [hm] at hP hL
  have hAD := F.hAng
  have hα := hAD.hα
  have hβ := hAD.hβ
  have hγd := hAD.hγdef
  have hαβ := hAD.hαβ
  obtain ⟨e1, e2, e3⟩ := hL
  -- the flank norms are the two flank distances, in the IsFlankPair order
  have hx : ∀ q : Fin 3, ‖(D.tile i).pts q - F.P‖ = dist ((D.tile i).pts q) F.P :=
    fun q => (dist_eq_norm _ _).symm
  rcases hUW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hx, hx]
    unfold NearBaseBridge.Perm3 at hP
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    refine ⟨fun hg => ?_, fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact Or.inl ⟨h1, h2⟩
      | exact Or.inr ⟨h1, h2⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
  · rw [hx, hx]
    unfold NearBaseBridge.Perm3 at hP
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    refine ⟨fun hg => ?_, fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact Or.inl ⟨h2, h1⟩
      | exact Or.inr ⟨h2, h1⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)

/-- `pprime_band_edge` with the tile's data exposed: the band tile `j`, its corner `m'` at P′, its
flank pair `(Lε·uR, W')`, and its band-side position. -/
theorem pprime_band_tile (F : HFrame D e f α β γ) (hK : Present D F.K) :
    ∃ (j : Fin N) (m' : Fin 3) (W' : Plane) (Lε : ℝ), (D.tile j).pts m' = F.P ∧
      IsFlankPair (D.tile j) m' F.P (Lε • F.uR) W' ∧ 0 < Lε ∧
      (∀ q, F.h ((D.tile j).pts q) ≤ F.h F.P) ∧
      ∃ ε ∈ F.band, EdgeIs D ε F.P (F.P + Lε • F.uR) := by
  classical
  have hK' := hK
  obtain ⟨k, hk⟩ := hK
  set Q1 := F.V + F.P - F.A with hQ1
  have hkr : Set.range (D.tile k).pts = {F.P, Q1, F.V} := by
    rw [hk]; unfold HFrame.K; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨m, hm⟩ := Erdos634.MarchInduction.mem_range_of_eq hkr (Set.mem_insert _ _)
  have hflank : IsFlankPair (D.tile k) m F.P (Q1 - F.P) (F.V - F.P) := by
    rcases Erdos634.MarchInduction.vertex_data_of_range hkr hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  obtain ⟨j, -, hPj, hcase⟩ := flank_neighbour_dissection D.toDissection F.hPint hm hflank
  rcases hcase with ⟨m', hm', U', W', hUW', S, hS, hQU, hside⟩ | ⟨m', -, hmpos, -, -⟩
  swap
  · exfalso
    obtain ⟨m'', hm''⟩ := pprime_vertex_of_mem F hK' j hPj
    exact NearBaseVertex.vertex_not_edge (D.tile j) m'' hm'' m' hmpos
  -- `Q₁ − P′ = c·uR`
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by
    have := F.hef; have : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
    positivity
  have hQ : Q1 - F.P = ((f : ℝ) ^ 2) • F.uR := by
    have : Q1 - F.P = F.V - F.A := by rw [hQ1]; abel
    rw [this, F.hV, add_sub_cancel_left]
  set Lε := (f : ℝ) ^ 2 / S with hLε
  have hLpos : 0 < Lε := by positivity
  have hU' : U' = Lε • F.uR := by
    have h1 : S • U' = ((f : ℝ) ^ 2) • F.uR := by rw [← hQU, hQ]
    have h2 : U' = S⁻¹ • (S • U') := by rw [smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
    rw [h2, h1, smul_smul, hLε, div_eq_inv_mul]
  have hnU' : ‖U'‖ = Lε := by
    rw [hU', norm_smul, F.huR, mul_one, Real.norm_of_nonneg hLpos.le]
  -- the side: `h(W') < 0`
  have hVP : 0 < F.h (F.V - F.P) := by
    have hhV : F.h F.V = F.h F.A := by
      rw [F.hV, map_add, map_smul, F.hhuR, smul_zero, add_zero]
    rw [map_sub, hhV]; linarith [F.hhP]
  have hW' : F.h W' < 0 := by
    have hs2 : cross F.uR W' * cross F.uR (F.V - F.P) < 0 := by
      rw [hQ, cross_smul_left', cross_smul_left'] at hside
      have e3 : (f : ℝ) ^ 2 * cross F.uR W' * ((f : ℝ) ^ 2 * cross F.uR (F.V - F.P))
          = ((f : ℝ) ^ 2 * (f : ℝ) ^ 2) * (cross F.uR W' * cross F.uR (F.V - F.P)) := by ring
      rw [e3] at hside
      by_contra hc; push Not at hc
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ (f : ℝ) ^ 2 * (f : ℝ) ^ 2) hc
      linarith
    have hp := h_prop F W' (F.V - F.P)
    by_contra hc; push Not at hc
    have : 0 ≤ cross F.uR (F.V - F.P) ^ 2 * F.h W' := by positivity
    have e4 : cross F.uR (F.V - F.P) ^ 2 * F.h W'
        = cross F.uR (F.V - F.P) * (cross F.uR W' * F.h (F.V - F.P)) := by rw [← hp]; ring
    rw [e4] at this
    have : cross F.uR W' * cross F.uR (F.V - F.P) * F.h (F.V - F.P) < 0 :=
      mul_neg_of_neg_of_pos hs2 hVP
    nlinarith
  -- the vertices of tile `j`
  have hhU : F.h (F.P + U') = F.h F.P := by
    rw [map_add, hU', map_smul, F.hhuR, smul_zero, add_zero]
  have hhW : F.h (F.P + W') < F.h F.P := by rw [map_add]; linarith
  have hdist : dist (F.P + U') F.P = Lε := by
    rw [dist_eq_norm, add_sub_cancel_left, hnU']
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hmem : ∀ q : Fin 3, q ≠ m' → (D.tile j).pts q = F.P + U' →
      (Lε = (e : ℝ) * f ∨ Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ Lε = (f : ℝ) ^ 2) := by
    intro q hq hqU
    have := NearBaseBridge.tile_dist_mem (D.tiles_congruent j) F.hM.hs0 F.hM.hs1 F.hM.hs2 q m' hq
    rw [hqU, hm', hdist] at this
    exact this
  have hband : ∀ q : Fin 3, F.h ((D.tile j).pts q) ≤ F.h F.P := by
    intro q
    rcases fin3_cases3 m' q with rfl | rfl | rfl
    · rw [hm']
    · rcases hUW' with ⟨h1, -⟩ | ⟨-, h2⟩
      · have : (D.tile j).pts (m' + 1) = F.P + U' := by rw [h1]; abel
        rw [this, hhU]
      · have : (D.tile j).pts (m' + 1) = F.P + W' := by rw [h2]; abel
        rw [this]; exact hhW.le
    · rcases hUW' with ⟨-, h2⟩ | ⟨h1, -⟩
      · have : (D.tile j).pts (m' + 2) = F.P + W' := by rw [h2]; abel
        rw [this]; exact hhW.le
      · have : (D.tile j).pts (m' + 2) = F.P + U' := by rw [h1]; abel
        rw [this, hhU]
  have hUW2 : IsFlankPair (D.tile j) m' F.P (Lε • F.uR) W' := by rw [← hU']; exact hUW'
  refine ⟨j, m', W', Lε, hm', hUW2, hLpos, hband, ?_⟩
  rcases hUW' with ⟨h1, -⟩ | ⟨h1, -⟩
  · have hq : (D.tile j).pts (m' + 1) = F.P + U' := by rw [h1]; abel
    refine ⟨(j, m'), ?_, ?_⟩
    · show (j, m') ∈ D.toDissection.lineChain F.h (F.h F.P)
      rw [Dissection.mem_lineChain]
      refine ⟨by simp only [hm'], by simp only; rw [hq, hhU], fun q => hband q⟩
    · show ({(D.tile j).pts m', (D.tile j).pts (m' + 1)} : Set Plane) = {F.P, F.P + Lε • F.uR}
      rw [hm', hq, hU']
  · have hq : (D.tile j).pts (m' + 2) = F.P + U' := by rw [h1]; abel
    refine ⟨(j, m' + 2), ?_, ?_⟩
    · show (j, m' + 2) ∈ D.toDissection.lineChain F.h (F.h F.P)
      rw [Dissection.mem_lineChain]
      refine ⟨by simp only; rw [hq, hhU], by simp only; rw [fin3_add_two_add_one, hm'],
        fun q => hband q⟩
    · show ({(D.tile j).pts (m' + 2), (D.tile j).pts (m' + 2 + 1)} : Set Plane)
        = {F.P, F.P + Lε • F.uR}
      rw [fin3_add_two_add_one, hm', hq, hU', Set.pair_comm]

/-- **R4 (a), second clause, at `a < b` (`e² + ef < f²`): the first band-side edge on ℓ⁺ from P′
is a `b`-edge or a `c`-edge, never an `a`-edge** — `pprime_order` minus its `T₂+P′` clause, at these
members, WITHOUT trace covering and WITHOUT a sector-measure lemma.  The band tile `Y` across `K`'s
ℓ⁺-flank (`pprime_band_tile`) and the tile `Z` across `T₃`'s P′J₁ (`pprime_across_J1`, which lays the
whole `a`-edge) are not `T₂, T₃, K` (band side; `J₁` a vertex of `Z`); the counts at P′
(`pprime_figure_cases`: `{γ}` or `{β, α, α}` in the residual) force `Y = Z` when the residual is
`{γ}`, and `Y ∈ {α, β}` otherwise; flank lengths (`flank_lengths`), `J₁ − P′ ∦ uR`
(`J1_not_along_uR`) and the whole `a` on P′J₁ exclude `a` on ℓ⁺. -/
theorem pprime_band_edge_not_a (F : HFrame D e f α β γ) (hK : Present D F.K)
    (hab : (e : ℝ) * f < (f : ℝ) ^ 2 - (e : ℝ) ^ 2) :
    ∃ ε ∈ F.band, ∃ Lε : ℝ, (Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ Lε = (f : ℝ) ^ 2) ∧
      EdgeIs D ε F.P (F.P + Lε • F.uR) := by
  classical
  obtain ⟨j, m', W', Lε, hm', hUW, hLpos, hband, ε, hε, hE⟩ := pprime_band_tile F hK
  refine ⟨ε, hε, Lε, ?_, hE⟩
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hnU : ‖Lε • F.uR‖ = Lε := by rw [norm_smul, F.huR, mul_one, Real.norm_of_nonneg hLpos.le]
  have hJP : ‖F.A + ((f : ℝ) ^ 2) • F.uL - F.P‖ = (e : ℝ) * f := by
    rw [← dist_eq_norm, dist_comm]; exact F.hPJ1
  have hPJ : dist F.P (F.A + ((f : ℝ) ^ 2) • F.uL) = (e : ℝ) * f := F.hPJ1
  -- the known tiles
  have hK' := hK
  obtain ⟨i3, z, h3, hz3, mz, W'', hmz, hUWz, -⟩ := pprime_across_J1 F hK hab
  obtain ⟨i2, h2⟩ := F.hT2
  obtain ⟨k, hk⟩ := hK'
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  have hAV : dist F.A F.V = (f : ℝ) ^ 2 := by rw [F.hV]; exact dist_self_add_unit F.huR hc0.le
  have hAJ : dist F.A (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 :=
    dist_self_add_unit F.huL hc0.le
  have h2' : Set.range (D.tile i2).pts = {F.P, F.A, F.V} := by
    rw [h2]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have h3' : Set.range (D.tile i3).pts = {F.P, F.A, F.A + ((f : ℝ) ^ 2) • F.uL} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hk' : Set.range (D.tile k).pts = {F.P, F.V, F.V + F.P - F.A} := by
    rw [hk]; unfold HFrame.K; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hVQ : dist F.V (F.V + F.P - F.A) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [← F.hAP, dist_comm F.V, dist_comm F.A F.P, dist_eq_norm, dist_eq_norm]
    congr 1; abel
  have g2 : (D.tile i2).localAngle F.P = γ := (hloc h2').2.2 hAV
  have g3 : (D.tile i3).localAngle F.P = γ := (hloc h3').2.2 hAJ
  have gk : (D.tile k).localAngle F.P = β := (hloc hk').2.1 hVQ
  -- the band tile is none of `T₂, T₃, K`
  have hhV : F.h F.V = F.h F.A := by rw [F.hV, map_add, map_smul, F.hhuR, smul_zero, add_zero]
  have hPA := F.hhP
  have hj2 : j ≠ i2 := by
    rintro rfl
    obtain ⟨q, hq⟩ : F.A ∈ Set.range (D.tile j).pts := by rw [h2']; simp
    have := hband q; rw [hq] at this; linarith
  have hj3 : j ≠ i3 := by
    rintro rfl
    obtain ⟨q, hq⟩ : F.A ∈ Set.range (D.tile j).pts := by rw [h3']; simp
    have := hband q; rw [hq] at this; linarith
  have hjk : j ≠ k := by
    rintro rfl
    obtain ⟨q, hq⟩ : F.V ∈ Set.range (D.tile j).pts := by rw [hk']; simp
    have := hband q; rw [hq, hhV] at this; linarith
  -- `J₁` is a vertex of `Z`, so `Z` is neither `T₂` nor `K`
  have hJz : F.A + ((f : ℝ) ^ 2) • F.uL ∈ Set.range (D.tile z).pts := by
    rcases hUWz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨mz + 1, sub_left_inj.mp h1.symm⟩
    · exact ⟨mz + 2, sub_left_inj.mp h1.symm⟩
  have hJA : F.A + ((f : ℝ) ^ 2) • F.uL ≠ F.A := by
    intro h; rw [h, dist_self] at hAJ; linarith
  have hJPne : F.A + ((f : ℝ) ^ 2) • F.uL ≠ F.P := by
    intro h; rw [h, dist_self] at hPJ; linarith
  have hJV : F.A + ((f : ℝ) ^ 2) • F.uL ≠ F.V := fun h => V_ne_J1 F h.symm
  have hJQ : F.A + ((f : ℝ) ^ 2) • F.uL ≠ F.V + F.P - F.A := by
    intro h
    have : dist F.P (F.A + ((f : ℝ) ^ 2) • F.uL) = (f : ℝ) ^ 2 := by
      rw [h, dist_eq_norm, show F.P - (F.V + F.P - F.A) = F.A - F.V by abel, ← dist_eq_norm, hAV]
    rw [hPJ] at this; exact hacd this
  have hz2 : z ≠ i2 := by
    rintro rfl
    rw [h2'] at hJz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJz
    rcases hJz with h | h | h
    · exact hJPne h
    · exact hJA h
    · exact hJV h
  have hzk : z ≠ k := by
    rintro rfl
    rw [hk'] at hJz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJz
    rcases hJz with h | h | h
    · exact hJPne h
    · exact hJV h
    · exact hJQ h
  have hi23 : i2 ≠ i3 := by
    intro h
    have hVm : F.V ∈ Set.range (D.tile i3).pts := by rw [← h, h2']; simp
    rw [h3'] at hVm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hVm
    rcases hVm with h' | h' | h'
    · have := F.hVP; rw [h', dist_self] at this; linarith
    · rw [h', dist_self] at hAV; linarith
    · exact hJV h'.symm
  -- angles and flank lengths of `Y` (tile `j`) and `Z` (tile `z`)
  have hYang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' j m'
  rw [hm'] at hYang
  have hZang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
  rw [hmz] at hZang
  have hflY := flank_lengths F hm' hUW
  rw [hnU] at hflY
  have hflZ := flank_lengths F hmz hUWz
  rw [hJP] at hflZ
  have memS : ∀ (θ : ℝ) (i : Fin N), (D.tile i).localAngle F.P = θ →
      i ∈ ({i | (D.tile i).localAngle F.P = θ} : Finset (Fin N)) := fun θ i h => by simp [h]
  -- if `Z = Y`, the other flank of `Y` is the whole `a`-edge `P′J₁`
  have hsame : z = j → ‖W'‖ = (e : ℝ) * f := by
    intro hzj
    subst hzj
    have hmm : mz = m' := (D.tile _).indep.injective (hmz.trans hm'.symm)
    subst hmm
    rcases flank_mem hUW hUWz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (J1_not_along_uR F hLpos)
    · rw [← h1]; exact hJP
  obtain ⟨-, -, hcases⟩ := pprime_figure_cases F ⟨k, hk⟩
  rcases hcases with ⟨hA0, hB1, hC3⟩ | ⟨hA2, hB2, hC2⟩
  · -- residual `{γ}`: `Y` and `Z` are both the residual `γ`-tile
    have notα : ∀ i, (D.tile i).localAngle F.P ≠ α := by
      intro i h; have := Finset.card_pos.mpr ⟨i, memS α i h⟩; omega
    have notβ : ∀ i, i ≠ k → (D.tile i).localAngle F.P ≠ β := by
      intro i hik h
      have hsub : ({k, i} : Finset (Fin N)) ⊆
          ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact memS β _ gk
        · exact memS β _ h
      have := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hik)] at this; omega
    have hYg : (D.tile j).localAngle F.P = γ := by
      rcases hYang with h | h | h
      · exact absurd h (notα j)
      · exact absurd h (notβ j hjk)
      · exact h
    have hZg : (D.tile z).localAngle F.P = γ := by
      rcases hZang with h | h | h
      · exact absurd h (notα z)
      · exact absurd h (notβ z hzk)
      · exact h
    have hzj : z = j := by
      have hsub : ({i2, i3, j} : Finset (Fin N)) ⊆
          ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact memS γ _ g2
        · exact memS γ _ g3
        · exact memS γ _ hYg
      have hcard : ({i2, i3, j} : Finset (Fin N)).card = 3 :=
        Finset.card_eq_three.mpr ⟨i2, i3, j, hi23, Ne.symm hj2, Ne.symm hj3, rfl⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; omega)
      have hzmem : z ∈ ({i2, i3, j} : Finset (Fin N)) := by rw [heq]; exact memS γ _ hZg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
      rcases hzmem with h | h | h
      · exact absurd h hz2
      · exact absurd h hz3
      · exact h
    have hW := hsame hzj
    rcases hflY.1 hYg with ⟨-, h2⟩ | ⟨h1, -⟩
    · exfalso; rw [hW] at h2; exact habd h2
    · left; exact h1
  · -- residual `{β, α, α}`: `Y` and `Z` are `α` or `β`
    have hSγ : ({i2, i3} : Finset (Fin N))
        = ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
      have hsub : ({i2, i3} : Finset (Fin N)) ⊆
          ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact memS γ _ g2
        · exact memS γ _ g3
      exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hi23]; omega)
    have notγ : ∀ i, i ≠ i2 → i ≠ i3 → (D.tile i).localAngle F.P ≠ γ := by
      intro i h2i h3i h
      have := memS γ i h
      rw [← hSγ] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h' | h'
      · exact h2i h'
      · exact h3i h'
    rcases hYang with h | h | h
    · rcases hflY.2.2 h with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; exact h1
      · right; exact h1
    · rcases hflY.2.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
      · exfalso
        by_cases hzj : z = j
        · have hW := hsame hzj; rw [hW] at h2; exact hacd h2
        · have hSβ : ({k, j} : Finset (Fin N))
              = ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)) := by
            have hsub : ({k, j} : Finset (Fin N)) ⊆
                ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact memS β _ gk
              · exact memS β _ h
            exact Finset.eq_of_subset_of_card_le hsub
              (by rw [Finset.card_pair (Ne.symm hjk)]; omega)
          rcases hZang with h' | h' | h'
          · rcases hflZ.2.2 h' with ⟨h1', -⟩ | ⟨h1', -⟩
            · exact habd h1'
            · exact hacd h1'
          · have := memS β z h'
            rw [← hSβ] at this
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            rcases this with h'' | h''
            · exact hzk h''
            · exact hzj h''
          · exact notγ z hz2 hz3 h'
      · right; exact h1
    · exact absurd h (notγ j hj2 hj3)

/-! ## What remains of `pprime_order`, precisely (2026-09-24, after `pprime_band_edge_not_a`)

`pprime_order` = `pprime_band_edge` (PROVED) + (iii-a) `Lε ≠ a` + (iii-b) `Lε = c → T₂ + P′`.
  * (iii-a) is PROVED at `a < b` (`pprime_band_edge_not_a`).  At `b < a` the one missing input is
    (T): the tile across P′J₁ lays exactly `a` (`pprime_across_J1` needs `a < b` only to exclude a
    `b`-flank shorter than `a` along P′J₁; that exclusion is TRACE COVERING of `[P′, J₁]` + `a`
    unsplittable, the shared blocker of G-R3 / R2 G3).  The rest of the assembly is `b`-blind.
  * (iii-b), any member: with `Lε = c` the band tile `Y` is `α` (flanks `b, c`) or `β` (flanks
    `a, c`).  Missing: (I) identification — an `α`-corner at P′ with `c` on ℓ⁺ and its `b`-flank on the
    band side is `{P′, V + P′ − A, 2P′ − A}` (the `b`-flank must be along `P′ − A`, which makes angle `α`
    with `uR`), and the exclusion of `Y = Z` presenting `β` with `c` on ℓ⁺ and `a` on P′J₁ (true since
    the angle between `uR` and `J₁ − P′` is `γ ≠ β`: an unoriented-angle computation from the frame's
    distances, or a sector-measure lemma).  Neither is a corner-ORDER statement any more: the order
    (adjacency) at P′ is `flank_neighbour`, and the corner types in the residual are counted. -/

/-- The extra hypothesis of `pprime_across_J1` / `pprime_band_edge_not_a` (`a < b`, i.e.
`e² + ef < f²`) holds at coprime members `2 ≤ e ≤ f − 2`, e.g. `(3,5)` (`15 < 16`), `(2,5)`, `(4,7)`
(`28 < 33`); it fails at `(7,10)` (`70 > 51`, the `b < a` side). -/
theorem a_lt_b_members :
    Nat.Coprime 3 5 ∧ (3 : ℝ) * 5 < 5 ^ 2 - 3 ^ 2 ∧ Nat.Coprime 4 7 ∧ (4 : ℝ) * 7 < 7 ^ 2 - 4 ^ 2 ∧
      ¬ ((7 : ℝ) * 10 < 10 ^ 2 - 7 ^ 2) := by
  refine ⟨by decide, by norm_num, by decide, by norm_num, by norm_num⟩

/-! ## Vacuity rule for the generic engine

`pprime_vertex_of_mem` / `pprime_band_edge` are conditional on an `HFrame` (an m = 1 dissection in
branch (H)), which cannot be witnessed outright — its non-existence is the goal (glue header).  Their
generic engines are witnessed on a REAL dissection: `flank_neighbour_dissection`'s hypotheses hold
jointly at the interior vertex `(14, 2√15)` of the 63-piece `(2,3,4)` tiling. -/

theorem flank_neighbour_witness63 :
    ∃ (i : Fin CevianTiling63.tiles.length) (k : Fin 3),
      ((NearBaseBridge.D63).tile i).pts k = NearBaseBridge.x63 ∧
      ∃ j, j ≠ i ∧ NearBaseBridge.x63 ∈ ((NearBaseBridge.D63).tile j).carrier := by
  obtain ⟨i, k, hk⟩ := NearBaseBridge.x63_vertex
  obtain ⟨j, hji, hxj, -⟩ := flank_neighbour_dissection NearBaseBridge.D63.toDissection
    NearBaseBridge.x63_interior hk (Or.inl ⟨rfl, rfl⟩)
  exact ⟨i, k, hk, j, hji, hxj⟩

end Erdos634.Draft.HalfTurnR3R4Order

#print axioms Erdos634.Draft.HalfTurnR3R4Order.localAngle_mem_pi_of_mem
#print axioms Erdos634.Draft.HalfTurnR3R4Order.pprime_vertex_of_mem
#print axioms Erdos634.Draft.HalfTurnR3R4Order.pprime_figure_cases
#print axioms Erdos634.Draft.HalfTurnR3R4Order.h_prop
#print axioms Erdos634.Draft.HalfTurnR3R4Order.pprime_band_edge
#print axioms Erdos634.Draft.HalfTurnR3R4Order.flank_neighbour_witness63
#print axioms Erdos634.Draft.HalfTurnR3R4Order.J1_not_interior
#print axioms Erdos634.Draft.HalfTurnR3R4Order.pprime_across_J1
#print axioms Erdos634.Draft.HalfTurnR3R4Order.V_ne_J1
#print axioms Erdos634.Draft.HalfTurnR3R4Order.J1_not_along_uR
#print axioms Erdos634.Draft.HalfTurnR3R4Order.flank_lengths
#print axioms Erdos634.Draft.HalfTurnR3R4Order.pprime_band_tile
#print axioms Erdos634.Draft.HalfTurnR3R4Order.pprime_band_edge_not_a
#print axioms Erdos634.Draft.HalfTurnR3R4Order.a_lt_b_members
