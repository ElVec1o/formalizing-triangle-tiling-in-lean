-- Draft/HalfTurnR4Real.lean — R4 ((private working notes, not included)) in branch (H): the P′ order lemma
-- `HalfTurnR3R4Glue.pprime_order` PROVED at EVERY member (the `b < a` case by trace covering of
-- `[P′, J₁]`, `TraceCovering.wall_sum` + `Inflation.a_unsplittable`; the `T₂ + P′` clause by
-- identifying the `β`-tile across `P′J₁` as `Z₀ = (P′, J₁, P′ + J₁ − A)`), and its real-dissection
-- form via `MirrorStripR2Real.K_present_real`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Build (scratch oleans; never .lake): MirrorStripR2Real olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/HalfTurnR4Real.lean'
import Erdos634.Draft.MirrorStripR2Real

namespace Erdos634.Draft.HalfTurnR4Real

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.ApexPlacement (eq_smul_of_norms)

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- The third side of a tile whose sides at `x` are `p`, `q` is the remaining value `r` (the three
side values pairwise distinct). -/
theorem third_side (D : CongruentDissection N) {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hs0 : sideOpp D.model 0 = a) (hs1 : sideOpp D.model 1 = b)
    (hs2 : sideOpp D.model 2 = c) {i : Fin N} {x Y Z : Plane}
    (hr : Set.range (D.tile i).pts = {x, Y, Z}) (hY : dist Y x = a) (hZ : dist Z x = c) :
    dist Y Z = b := by
  obtain ⟨m, hm⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
  have hP := NearBaseBridge.tile_triple (D.tiles_congruent i) hs0 hs1 hs2 m
  rw [hm] at hP
  unfold NearBaseBridge.Perm3 at hP
  rcases MarchInduction.vertex_data_of_range hr hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at hP
  · rw [hY, hZ] at hP
    rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ |
      ⟨p1, p2, p3⟩ <;>
    first
      | exact p3
      | exact absurd p1 hab
      | exact absurd p1 hac
      | exact absurd p2 hbc.symm
      | exact absurd p2 hac.symm
      | exact absurd p1 hab.symm
  · rw [hY, hZ] at hP
    rw [dist_comm]
    rcases hP with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ |
      ⟨p1, p2, p3⟩ <;>
    first
      | exact p3
      | exact absurd p2 hab
      | exact absurd p2 hac
      | exact absurd p1 hbc.symm
      | exact absurd p1 hac.symm
      | exact absurd p2 hab.symm

/-! ## §1 (T): the tile across `P′J₁` lays exactly `a` — every member -/

/-- **(T) at `b < a`.**  The tile across `T₃`'s `a`-edge `P′J₁` cannot lay a `b`-flank there: the far
side of the wall `[P′, J₁]` is covered by whole edges totalling `a` (`TraceCovering.wall_sum`: `P′` is a
vertex of every tile containing it, the line leaves the target just after the leg point `J₁`), one of
them the `b`-flank, and `a` has no representation containing `b` (`Inflation.a_unsplittable`). -/
theorem across_J1_not_b (F : HFrame D e f α β γ) (hK : Present D F.K) {z : Fin N} {mz : Fin 3}
    {U W : Plane} (hmz : (D.tile z).pts mz = F.P) (hUW : IsFlankPair (D.tile z) mz F.P U W)
    {S : ℝ} (hS : 0 < S) (hJU : F.A + ((f : ℝ) ^ 2) • F.uL - F.P = S • U)
    (hside : cross (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) W
      * cross (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) (F.A - F.P) < 0)
    (hUb : ‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (hle : ‖U‖ ≤ (e : ℝ) * f) : False := by
  classical
  set J1 := F.A + ((f : ℝ) ^ 2) • F.uL with hJ1
  have hef := F.hef
  have he := F.he
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast hef
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  obtain ⟨habd, hacd, hbcd⟩ := sides_distinct F.hco F.he (by omega)
  have hba : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (e : ℝ) * f :=
    lt_of_le_of_ne (hUb ▸ hle) (Ne.symm habd)
  have hJP : ‖J1 - F.P‖ = (e : ℝ) * f := by rw [← dist_eq_norm, dist_comm]; exact F.hPJ1
  have hUe : U = (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / ((e : ℝ) * f)) • (J1 - F.P) :=
    eq_smul_of_norms hS hJU hJP hUb ha0
  -- the line `P′ + ℝ·u`, `u` the unit vector towards `J₁`
  set u : Plane := (1 / ((e : ℝ) * f)) • (J1 - F.P) with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_smul, hJP, Real.norm_of_nonneg (by positivity), one_div_mul_cancel ha0.ne']
  have hu0 : u ≠ 0 := TraceCovering.ne_zero_of_norm hu1
  have hJu : F.P + ((e : ℝ) * f) • u = J1 := by
    rw [hudef, smul_smul, mul_one_div_cancel ha0.ne', one_smul]; abel
  have hUu : U = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • u := by
    rw [hUe, hudef, smul_smul]; congr 1; field_simp
  -- the side functional: `T₃` (through `A`) on `{g ≥ g P′}`, `Z` on `{g ≤ g P′}`
  set ε0 := cross (J1 - F.P) (F.A - F.P) with hε0def
  have hε0 : ε0 ≠ 0 := by intro h; rw [h, mul_zero] at hside; exact lt_irrefl _ hside
  set g : Plane →ₗ[ℝ] ℝ := ε0 • crossL (J1 - F.P) with hgdef
  have happ : ∀ y, g y = ε0 * cross (J1 - F.P) y := fun y => by
    rw [hgdef, LinearMap.smul_apply, crossL_apply, smul_eq_mul]
  have hgu : g u = 0 := by rw [happ, hudef, cross_smul_right, cross_self', mul_zero, mul_zero]
  have hgA : g F.A - g F.P = ε0 * ε0 := by
    rw [happ, happ, ← mul_sub, ← cross_sub_right']
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, LinearMap.zero_apply, LinearMap.zero_apply, sub_zero] at hgA
    exact hε0 (mul_self_eq_zero.mp hgA.symm)
  -- `T₃`'s edge `[P′, J₁]`
  obtain ⟨i3, h3⟩ := F.hT3
  have h3r : Set.range (D.tile i3).pts = {F.P, J1, F.A} := by
    rw [h3]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨k0, hk0⟩ := MarchInduction.mem_range_of_eq h3r (Set.mem_insert _ _)
  obtain ⟨k1, hk1⟩ := MarchInduction.mem_range_of_eq h3r
    (show J1 ∈ ({F.P, J1, F.A} : Set Plane) by simp)
  have hPJne : F.P ≠ J1 := by intro h; rw [← h, sub_self, norm_zero] at hJP; linarith
  have hkne : k0 ≠ k1 := by rintro rfl; exact hPJne (hk0.symm.trans hk1)
  obtain ⟨m3, hm3⟩ := (D.tile i3).pair_eq_edge hkne
  have hJmem : J1 ∈ D.target.carrier := by
    rw [← hk1]; exact MarchInduction.pts_mem_target D.toDissection i3 k1
  have hseg : ∀ x ∈ Set.Ioo 0 ((e : ℝ) * f),
      F.P + x • u ∈ openSegment ℝ F.P J1 := by
    intro x hx
    refine ⟨1 - x / ((e : ℝ) * f), x / ((e : ℝ) * f), ?_, ?_, by ring, ?_⟩
    · rw [sub_pos, div_lt_one ha0]; exact hx.2
    · exact div_pos hx.1 ha0
    · rw [← hJu, smul_add, smul_smul, div_mul_cancel₀ x ha0.ne']; module
  have hint : ∀ x ∈ Set.Ioo 0 ((e : ℝ) * f), F.P + x • u ∈ interior D.target.carrier :=
    fun x hx => D.target.convex.openSegment_interior_closure_subset_interior F.hPint
      (subset_closure hJmem) (hseg x hx)
  have hwall : ∀ x ∈ Set.Ioo 0 ((e : ℝ) * f), ∀ i, F.P + x • u ∉ interior (D.tile i).carrier := by
    intro x hx i
    have hmem : F.P + x • u ∈ (D.tile i3).edge m3 := by
      rw [← hm3, hk0, hk1]; exact openSegment_subset_segment ℝ _ _ (hseg x hx)
    exact D.toDissection.edge_point_not_interior hmem i
  -- no edge on the line passes through `P′` (a vertex of every tile containing it)
  have hs : ¬ TraceCovering.Straddled D.toDissection g (g F.P) (F.P + (0 : ℝ) • u) := by
    rintro ⟨ε, -, hstr⟩
    rw [zero_smul, add_zero] at hstr
    obtain ⟨hc2, hc0, hc1⟩ := openSeg_coords (D.tile ε.1) ε.2 hstr
    have hPm : F.P ∈ (D.tile ε.1).carrier := by
      rw [NearBaseVertex.mem_carrier_iff]; intro l
      rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
      · exact hc0.le
      · exact hc1.le
      · exact hc2.ge
    obtain ⟨q, hq⟩ := pprime_vertex_of_mem F hK ε.1 hPm
    refine NearBaseVertex.vertex_not_edge _ q hq (ε.2 + 2) (fun l hl => ?_)
    rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0
    · exact hc1
    · exact absurd rfl hl
  -- none through `J₁` (the line leaves the target just after the leg point `J₁`)
  have ht : ¬ TraceCovering.Straddled D.toDissection g (g F.P) (F.P + ((e : ℝ) * f) • u) := by
    refine TraceCovering.not_straddled_of_outside_after (fun _ => Iff.rfl) hg0 rfl hgu hu0 ?_
    intro t ht hmem
    apply J1_not_interior F
    refine D.target.convex.openSegment_interior_closure_subset_interior F.hPint
      (subset_closure hmem) ⟨1 - (e : ℝ) * f / t, (e : ℝ) * f / t, ?_, ?_, by ring, ?_⟩
    · rw [sub_pos, div_lt_one (by linarith)]; exact ht
    · exact div_pos ha0 (by linarith)
    · have ht0 : t ≠ 0 := by intro h; rw [h] at ht; linarith
      rw [← hJ1, ← hJu, smul_add, smul_smul, div_mul_cancel₀ _ ht0]; module
  have hsum := TraceCovering.wall_sum (D := D.toDissection) (f := g) (c := g F.P) hg0
    (fun _ => Iff.rfl) hg0 rfl hgu hu1 ha0.le hint hwall hs ht
  -- `Z`'s `b`-flank `[P′, P′ + b·u]` is one of the far edges
  obtain ⟨m', hm01, hm2⟩ : ∃ m' : Fin 3,
      (((D.tile z).pts m' = F.P ∧ (D.tile z).pts (m' + 1) = F.P + U) ∨
        ((D.tile z).pts m' = F.P + U ∧ (D.tile z).pts (m' + 1) = F.P)) ∧
      (D.tile z).pts (m' + 2) = F.P + W := by
    rcases hUW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨mz, Or.inl ⟨hmz, by rw [h1]; abel⟩, by rw [h2]; abel⟩
    · refine ⟨mz + 2, Or.inr ⟨by rw [h1]; abel, by rw [fin3_add_two_add_one, hmz]⟩, ?_⟩
      rw [fin3_add_two_add_two, h2]; abel
  have hgU : g (F.P + U) = g F.P := by
    rw [map_add, hUu, map_smul, hgu, smul_zero, add_zero]
  have hgW : g (F.P + W) < g F.P := by
    rw [map_add, happ W]
    have : ε0 * cross (J1 - F.P) W < 0 := by rw [mul_comm]; exact hside
    linarith
  have heM : (z, m') ∈ D.toDissection.lineChain g (g F.P) := by
    rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]; exact hgU
    · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]; exact hgU
    · rcases fin3_cases3 m' i with rfl | rfl | rfl
      · rcases hm01 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]; exact hgU.le
      · rcases hm01 with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]; exact hgU.le
      · rw [hm2]; exact hgW.le
  have hSeg : ∀ y, y = F.P ∨ y = F.P + U →
      y ∈ segment ℝ (F.P + (0 : ℝ) • u) (F.P + ((e : ℝ) * f) • u) := by
    rintro y (rfl | rfl)
    · convert left_mem_segment ℝ (F.P + (0 : ℝ) • u) (F.P + ((e : ℝ) * f) • u) using 1
      rw [zero_smul, add_zero]
    · rw [TraceCovering.segment_param, min_eq_left ha0.le, max_eq_right ha0.le, hUu]
      exact ⟨_, ⟨hb0.le, hba.le⟩, rfl⟩
  have hin : (D.tile z).edge m' ⊆
      segment ℝ (F.P + (0 : ℝ) • u) (F.P + ((e : ℝ) * f) • u) := by
    rw [Tri.edge]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      exact (convex_segment _ _).segment_subset (hSeg _ (by simp)) (hSeg _ (by simp))
  have hdM : dist ((D.tile z).pts m') ((D.tile z).pts (m' + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.P (F.P + U) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, hUb]
    rcases hm01 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  set s := (D.toDissection.lineChain g (g F.P)).filter
    (fun ε => (D.tile ε.1).edge ε.2 ⊆ segment ℝ (F.P + (0 : ℝ) • u) (F.P + ((e : ℝ) * f) • u))
    with hs_def
  have hmemS : (z, m') ∈ s := Finset.mem_filter.mpr ⟨heM, hin⟩
  rw [← Finset.add_sum_erase s _ hmemS] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (s.erase (z, m'))
    (fun ε => dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => MirrorStripR2Glue.edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
      = ((e * f : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hee]
    simp only at hsum hdM
    rw [hdM] at hsum
    linarith
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = e * f := by
    exact_mod_cast hreal
  obtain ⟨-, hQ, -⟩ := Inflation.a_unsplittable e f (f ^ 2 - e ^ 2) P' (Q' + 1) R' (by omega)
    (by omega) F.hco (Nat.sub_add_cancel hee) hnat
  omega

/-- **`pprime_across_J1` at EVERY member** (the `a < b` hypothesis removed by (T)): the tile across
`T₃`'s `a`-edge `P′J₁` lays exactly the whole `a`-edge `[P′, J₁]`. -/
theorem pprime_across_J1_all (F : HFrame D e f α β γ) (hK : Present D F.K) :
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
  have hac : (e : ℝ) * f < (f : ℝ) ^ 2 := by nlinarith
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
    · exact (across_J1_not_b F hK hmz hUW hS hJU hside h hle).elim
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


/-! ## §2 `pprime_order` at every member -/

/-- **R4 (a), `HalfTurnR3R4Glue.pprime_order`, PROVED at every coprime member `2 ≤ e ≤ f − 2`.**  In
(H), the first band-side edge on `ℓ⁺` from `P′` has length `b` or `c`, never `a`, and if it is `c` its
tile is `T₂ + P′`.  The tile `Y` across `K`'s `ℓ⁺`-flank (`pprime_band_tile`) and the tile `Z` across
`T₃`'s `P′J₁` (`pprime_across_J1_all`: the whole `a`-edge) are counted at `P′`
(`pprime_figure_cases`): with residual `{γ}`, `Y = Z` and `Y`'s flank on `ℓ⁺` is its `b`; with
`{β, α, α}`, `Z` is the `β`-tile `Z₀ = (P′, J₁, P′ + J₁ − A)` (`third_vertex_cross`), so `Y ≠ Z`
(`uR ≠ uL`), `Y` is an `α`-tile, and with `c` on `ℓ⁺` it is `T₂ + P′` (`TileIdent.pprime_alpha_ident`). -/
theorem pprime_order' (F : HFrame D e f α β γ) (hK : Present D F.K) :
    ∃ ε ∈ F.band, ∃ Lε : ℝ, (Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ Lε = (f : ℝ) ^ 2) ∧
      EdgeIs D ε F.P (F.P + Lε • F.uR) ∧ (Lε = (f : ℝ) ^ 2 → Present D F.T2P) := by
  classical
  obtain ⟨j, m', W', Lε, hm', hUW, hLpos, hband, ε, hε, hE⟩ := pprime_band_tile F hK
  refine ⟨ε, hε, Lε, ?_⟩
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
  obtain ⟨i3, z, h3, hz3, mz, W'', hmz, hUWz, hsidez⟩ := pprime_across_J1_all F hK
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
  -- if `Z = Y`, `Y`'s other flank is `P′J₁` and `Z`'s other flank is `Y`'s `ℓ⁺`-flank
  have hsame : z = j → W' = F.A + ((f : ℝ) ^ 2) • F.uL - F.P ∧ W'' = Lε • F.uR := by
    intro hzj
    subst hzj
    have hmm : mz = m' := (D.tile _).indep.injective (hmz.trans hm'.symm)
    subst hmm
    rcases flank_mem hUW hUWz with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact absurd h1 (J1_not_along_uR F hLpos)
    · exact ⟨h1.symm, h2⟩
  have hmain : (D.tile j).localAngle F.P = α ∨ Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    obtain ⟨-, -, hcases⟩ := pprime_figure_cases F ⟨k, hk⟩
    rcases hcases with ⟨hA0, hB1, hC3⟩ | ⟨hA2, hB2, hC2⟩
    · -- residual `{γ}`: `Y = Z`, and `Y`'s flank on `ℓ⁺` is its `b`
      right
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
      have hW := (hsame hzj).1
      rcases hflY.1 hYg with ⟨-, h2⟩ | ⟨h1, -⟩
      · exfalso; rw [hW, hJP] at h2; exact habd h2
      · exact h1
    · -- residual `{β, α, α}`: `Y` is `α` (a `β` there would be `Z = Z₀`, whose other flank is `c·uL`)
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
      · exact Or.inl h
      · exfalso
        -- `Z` is the `β`-tile
        have hzβ : (D.tile z).localAngle F.P = β := by
          rcases hZang with h' | h' | h'
          · rcases hflZ.2.2 h' with ⟨h1', -⟩ | ⟨h1', -⟩
            · exact absurd h1' habd
            · exact absurd h1' hacd
          · exact h'
          · exact absurd h' (notγ z hz2 hz3)
        have hSβ : ({k, z} : Finset (Fin N))
            = ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)) := by
          have hsub : ({k, z} : Finset (Fin N)) ⊆
              ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact memS β _ gk
            · exact memS β _ hzβ
          exact Finset.eq_of_subset_of_card_le hsub
            (by rw [Finset.card_pair (Ne.symm hzk)]; omega)
        have hzj : z = j := by
          have := memS β j h
          rw [← hSβ] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h' | h'
          · exact absurd h' hjk
          · exact h'.symm
        have hW'' := (hsame hzj).2
        -- `Z = Z₀`: its third vertex is `P′ + J₁ − A`
        have hW''c : ‖W''‖ = (f : ℝ) ^ 2 := by
          rcases hflZ.2.1 hzβ with ⟨-, h2'⟩ | ⟨h1', -⟩
          · exact h2'
          · exact absurd h1' hacd
        have hrz : Set.range (D.tile z).pts = {F.P, F.A + ((f : ℝ) ^ 2) • F.uL, F.P + W''} := by
          rw [ApexPlacement.range_of_flank hmz hUWz]; congr 2; abel
        have hopp : dist (F.A + ((f : ℝ) ^ 2) • F.uL) (F.P + W'') = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
          third_side D habd hacd hbcd F.hM.hs0 F.hM.hs1 F.hM.hs2 hrz (by rw [dist_comm]; exact hPJ)
            (by rw [dist_eq_norm, add_sub_cancel_left, hW''c])
        have hZ0 : F.P + W'' = F.P + ((F.A + ((f : ℝ) ^ 2) • F.uL) - F.A) := by
          apply third_vertex_cross (X := F.P) (Y := F.A + ((f : ℝ) ^ 2) • F.uL)
          · exact hJPne.symm
          · rw [add_sub_cancel_left, add_sub_cancel_left,
              show (F.A + ((f : ℝ) ^ 2) • F.uL) - F.A
                = (F.A + ((f : ℝ) ^ 2) • F.uL - F.P) - (F.A - F.P) by abel,
              cross_sub_right', cross_self', zero_sub, mul_neg]
            linarith
          · have e1 : dist F.P (F.P + W'') = (f : ℝ) ^ 2 := by
              rw [dist_comm, dist_eq_norm, add_sub_cancel_left, hW''c]
            have e2 : dist F.P (F.P + ((F.A + ((f : ℝ) ^ 2) • F.uL) - F.A)) = (f : ℝ) ^ 2 := by
              rw [dist_comm, dist_eq_norm, add_sub_cancel_left, add_sub_cancel_left, norm_smul,
                F.huL, mul_one, Real.norm_of_nonneg hc0.le]
            rw [e1, e2]
          · rw [hopp, dist_comm, dist_eq_norm,
              show F.P + ((F.A + ((f : ℝ) ^ 2) • F.uL) - F.A) - (F.A + ((f : ℝ) ^ 2) • F.uL)
                = F.P - F.A by abel, ← dist_eq_norm, dist_comm, F.hAP]
        have hW0 : W'' = ((f : ℝ) ^ 2) • F.uL := by
          have := add_left_cancel hZ0; rw [this]; abel
        -- then `Lε·uR = c·uL`, so `uR = uL` and `V = J₁`
        rw [hW0] at hW''
        have hL : Lε = (f : ℝ) ^ 2 := by
          have := congrArg norm hW''
          rw [hnU, norm_smul, F.huL, mul_one, Real.norm_of_nonneg hc0.le] at this
          exact this.symm
        rw [hL] at hW''
        have huRL : F.uR = F.uL := smul_right_injective _ hc0.ne' hW''.symm
        apply V_ne_J1 F
        rw [F.hV, huRL]
      · exact absurd h (notγ j hj2 hj3)
  rcases hmain with hα | hLb
  · rcases hflY.2.2 hα with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨Or.inl h1, hE, fun hc => absurd (h1.symm.trans hc) hbcd⟩
    · refine ⟨Or.inr h1, hE, fun _ => ?_⟩
      have hUW' : IsFlankPair (D.tile j) m' F.P (((f : ℝ) ^ 2) • F.uR) W' := by
        rw [← h1]; exact hUW
      exact TileIdent.pprime_alpha_ident F hm' hUW' hband hα
  · exact ⟨Or.inl hLb, hE, fun hc => absurd (hLb.symm.trans hc) hbcd⟩

/-- **R4 (a) for EVERY real `m = 1` dissection.**  Every congruent dissection of the `m = 1` base-β
target (coprime `2 ≤ e ≤ f − 2`) is in branch (H) (`K_present_real`), and in its apex frame the first
band edge on `ℓ⁺` from `P′` is `b` or `c`, a `c` being laid by `T₂ + P′`. -/
theorem pprime_order_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, Present D F.K ∧
      ∃ ε ∈ F.band, ∃ Lε : ℝ, (Lε = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨ Lε = (f : ℝ) ^ 2) ∧
        EdgeIs D ε F.P (F.P + Lε • F.uR) ∧ (Lε = (f : ℝ) ^ 2 → Present D F.T2P) := by
  obtain ⟨F, -, hK⟩ := K_present_real h
  exact ⟨F, hK, pprime_order' F hK⟩


end Erdos634.Draft.HalfTurnR4Real

/-! ## §3 The chain of translates along `r` and `ℓ` -/

namespace Erdos634.Draft.HalfTurnR3R4Glue.HFrame

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.MirrorStripR2Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-- The chain point `kV = A + k·c·uR` on the mismatch ray `r`. -/
noncomputable def Vk (k : ℕ) : Plane := F.A + ((k : ℝ) * (f : ℝ) ^ 2) • F.uR
/-- The point `Q_k = P′ + k·c·uR` of `ℓ`. -/
noncomputable def Qk (k : ℕ) : Plane := F.P + ((k : ℝ) * (f : ℝ) ^ 2) • F.uR
/-- `L_k = T₂ + k(V − A) = (kV, (k+1)V, Q_k)` (`L₀ = T₂`). -/
def Lc (k : ℕ) : Set Plane := {F.Vk k, F.Vk (k + 1), F.Qk k}
/-- `K_k = K + k(V − A) = ((k+1)V, Q_k, Q_{k+1})` (`K₀ = K`). -/
def Kk (k : ℕ) : Set Plane := {F.Vk (k + 1), F.Qk k, F.Qk (k + 1)}

theorem Vk_zero : F.Vk 0 = F.A := by simp [HFrame.Vk]
theorem Vk_one : F.Vk 1 = F.V := by simp [HFrame.Vk, F.hV]
theorem Qk_zero : F.Qk 0 = F.P := by simp [HFrame.Qk]

theorem Vk_succ_sub (k : ℕ) : F.Vk (k + 1) - F.Vk k = ((f : ℝ) ^ 2) • F.uR := by
  simp only [HFrame.Vk]; push_cast; module
theorem Qk_succ_sub (k : ℕ) : F.Qk (k + 1) - F.Qk k = ((f : ℝ) ^ 2) • F.uR := by
  simp only [HFrame.Qk]; push_cast; module
theorem Qk_sub_Vk (k : ℕ) : F.Qk k - F.Vk k = F.P - F.A := by
  simp only [HFrame.Qk, HFrame.Vk]; abel
theorem Vk_succ_sub_Qk (k : ℕ) :
    F.Vk (k + 1) - F.Qk k = ((f : ℝ) ^ 2) • F.uR - (F.P - F.A) := by
  simp only [HFrame.Qk, HFrame.Vk]; push_cast; module

theorem Vk_two_sub (k : ℕ) : F.Vk (k + 2) - F.Vk (k + 1) = ((f : ℝ) ^ 2) • F.uR := by
  simp only [HFrame.Vk]; push_cast; module
theorem Qk_two_sub (k : ℕ) : F.Qk (k + 2) - F.Qk (k + 1) = ((f : ℝ) ^ 2) • F.uR := by
  simp only [HFrame.Qk]; push_cast; module
theorem Vk_two_sub_Qk (k : ℕ) :
    F.Vk (k + 2) - F.Qk (k + 1) = ((f : ℝ) ^ 2) • F.uR - (F.P - F.A) := by
  simp only [HFrame.Qk, HFrame.Vk]; push_cast; module

theorem hw_norm : ‖F.P - F.A‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [← dist_eq_norm, dist_comm]; exact F.hAP
theorem hcw_norm : ‖((f : ℝ) ^ 2) • F.uR - (F.P - F.A)‖ = (e : ℝ) * f := by
  have : ((f : ℝ) ^ 2) • F.uR - (F.P - F.A) = F.V - F.P := by rw [F.hV]; abel
  rw [this, ← dist_eq_norm]; exact F.hVP
theorem c_normR : ‖((f : ℝ) ^ 2) • F.uR‖ = (f : ℝ) ^ 2 := by
  rw [norm_smul, F.huR, mul_one, Real.norm_of_nonneg (by positivity)]
theorem hw_neg : F.h (F.P - F.A) < 0 := by rw [map_sub]; linarith [F.hhP]
theorem uR_ne : F.uR ≠ 0 := TraceCovering.ne_zero_of_norm F.huR
theorem cross_uR_w : cross F.uR (F.P - F.A) ≠ 0 :=
  cross_ne_of_g F.h F.uR_ne F.hhuR F.hw_neg.ne
theorem cross_w_uR : cross (F.P - F.A) F.uR ≠ 0 := by
  rw [cross_anti]; exact neg_ne_zero.mpr F.cross_uR_w
theorem h_Vk (k : ℕ) : F.h (F.Vk k) = F.h F.A := by
  rw [HFrame.Vk, map_add, map_smul, F.hhuR, smul_zero, add_zero]
theorem h_Qk (k : ℕ) : F.h (F.Qk k) = F.h F.P := by
  rw [HFrame.Qk, map_add, map_smul, F.hhuR, smul_zero, add_zero]

/-- Cone coordinates along `ℓ`: `P′ + x·uR = A + σ·(f³uL) + τ·(R − A)` with `σ + τ = (1 + x/b)/f`. -/
theorem line_coords (FC : ApexPlacement.FrameCoords F) :
    ∃ s3 t3 s1 t1 : ℝ, 0 < s3 ∧ 0 < t3 ∧ 0 < s1 ∧ 0 < t1 ∧ s3 + t3 = 1 / (f : ℝ) ∧
      s1 + t1 = 1 / (f : ℝ) ∧ ∀ x : ℝ, F.P + x • F.uR = F.A +
        ((s3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s1) • (((f : ℝ) ^ 3) • F.uL)
          + (t3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * t1) • (F.R - F.A)) := by
  obtain ⟨s3, t3, hs3, ht3, hP, -, hsum3⟩ := FC.hP
  obtain ⟨s1, t1, hs1, ht1, hV, -, hsum1⟩ := FC.hV
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  refine ⟨s3, t3, s1, t1, hs3, ht3, hs1, ht1, hsum3, hsum1, fun x => ?_⟩
  have huR : F.uR = (1 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) •
      (s1 • (((f : ℝ) ^ 3) • F.uL) + t1 • (F.R - F.A)) := by
    rw [← hV, smul_smul, one_div_mul_cancel hb0.ne', one_smul]
  have hP' : F.P = F.A + (s3 • (((f : ℝ) ^ 3) • F.uL) + t3 • (F.R - F.A)) := by
    rw [← hP]; abel
  rw [hP', huR]
  rw [div_eq_mul_one_div x]
  module

/-- `ℓ` stays in the target only up to distance `(f − 1)·b` from `P′`. -/
theorem line_mem_bound (FC : ApexPlacement.FrameCoords F) {x : ℝ} (hx : 0 ≤ x)
    (hmem : F.P + x • F.uR ∈ D.target.carrier) :
    x ≤ ((f : ℝ) - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  obtain ⟨s3, t3, s1, t1, -, -, -, -, hs3, hs1, hL⟩ := F.line_coords FC
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hf0 : (0 : ℝ) < f := by linarith
  by_contra hc; push Not at hc
  apply FC.hout _ _ _ (hL x ▸ hmem)
  have e1 : s3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s1 + (t3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * t1)
      = (1 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) / (f : ℝ) := by
    have : s3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s1 + (t3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * t1)
        = (s3 + t3) + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (s1 + t1) := by ring
    rw [this, hs3, hs1]; field_simp
  rw [e1, lt_div_iff₀ hf0, one_mul]
  have : ((f : ℝ) - 1) < x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by rw [lt_div_iff₀ hb0]; exact hc
  linarith

/-- Points of `ℓ` from `P′` before distance `(f − 1)·b` are interior to the target. -/
theorem line_interior (FC : ApexPlacement.FrameCoords F) {x : ℝ} (hx : 0 ≤ x)
    (hlt : x < ((f : ℝ) - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    F.P + x • F.uR ∈ interior D.target.carrier := by
  obtain ⟨s3, t3, s1, t1, hs3', ht3', hs1', ht1', hs3, hs1, hL⟩ := F.line_coords FC
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hq : 0 ≤ x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := div_nonneg hx hb0.le
  have h1 := FC.hcone.inter (s3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s1)
    (t3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * t1) 1 (by positivity) (by positivity) one_pos (by
      have : s3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s1
          + (t3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * t1)
          = (1 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) / (f : ℝ) := by
        have : s3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * s1
            + (t3 + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * t1)
            = (s3 + t3) + x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (s1 + t1) := by ring
        rw [this, hs3, hs1]; field_simp
      rw [one_mul, this, div_lt_one hf0]
      have : x / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < (f : ℝ) - 1 := by rw [div_lt_iff₀ hb0]; exact hlt
      linarith)
  rw [show F.A + ((f : ℝ) ^ 3) • F.uL - F.A = ((f : ℝ) ^ 3) • F.uL by abel, one_smul] at h1
  rw [hL x]; exact h1

end Erdos634.Draft.HalfTurnR3R4Glue.HFrame

namespace Erdos634.Draft.HalfTurnR4Real

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}

/-- `f ∤ e²` at a coprime member `f ≥ 2`. -/
theorem f_not_dvd {e f : ℕ} (hco : Nat.Coprime e f) (hf : 2 ≤ f) {m : ℤ}
    (h : (e : ℤ) ^ 2 = (f : ℤ) * m) : False := by
  have hd : (f : ℤ) ∣ ((e ^ 2 : ℕ) : ℤ) := ⟨m, by push_cast; exact h⟩
  have hd' : f ∣ e ^ 2 := Int.natCast_dvd_natCast.mp hd
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 hco.symm) hd'
  omega

/-- `Q_k` never sits at the exit distance `(f − 1)·b` of `ℓ`. -/
theorem Qk_ne_exit (F : HFrame D e f α β γ) (k : ℕ) :
    (k : ℝ) * (f : ℝ) ^ 2 ≠ ((f : ℝ) - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  intro h
  have h' : ((k * f ^ 2 + e ^ 2 * f : ℕ) : ℝ) = ((f ^ 3 + e ^ 2 : ℕ) : ℝ) - ((f ^ 2 : ℕ) : ℝ) := by
    push_cast; linear_combination h
  have hz : ((k : ℤ) * (f : ℤ) ^ 2 + (e : ℤ) ^ 2 * f) = (f : ℤ) ^ 3 + (e : ℤ) ^ 2 - (f : ℤ) ^ 2 := by
    exact_mod_cast h'
  exact f_not_dvd F.hco (by have := F.hef; omega)
    (m := (k : ℤ) * f + (e : ℤ) ^ 2 + f - (f : ℤ) ^ 2) (by linear_combination -hz)

/-- The chain point `kV` never sits at the exit distance `f·b` of `r`. -/
theorem Vk_ne_exit (F : HFrame D e f α β γ) (k : ℕ) :
    (k : ℝ) * (f : ℝ) ^ 2 ≠ (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  intro h
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
  have h2 : (k : ℝ) * f = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : (f : ℝ) * ((k : ℝ) * f) = (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by linear_combination h
    exact mul_left_cancel₀ hf0.ne' this
  have hz : (k : ℤ) * f = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by exact_mod_cast h2
  exact f_not_dvd F.hco (by have := F.hef; omega) (m := (f : ℤ) - k) (by linear_combination hz)

/-- A chain point of the target lies strictly before the exit of `r`. -/
theorem Vk_lt (F : HFrame D e f α β γ) (k : ℕ) (hmem : F.Vk k ∈ D.target.carrier) :
    (k : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
  rcases lt_or_ge ((k : ℝ) * (f : ℝ) ^ 2) ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h' | h'
    · apply F.hrbase ((k : ℝ) * (f : ℝ) ^ 2 - (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) (by linarith)
      have : F.A + ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
          + ((k : ℝ) * (f : ℝ) ^ 2 - (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) • F.uR = F.Vk k := by
        rw [HFrame.Vk]; congr 2; ring
      rw [this]; exact hmem
    · exact Vk_ne_exit F k h'.symm

/-- A point `Q_k` of the target lies strictly before the exit of `ℓ`, so `k ≤ f − 2`. -/
theorem Qk_lt (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F) (k : ℕ)
    (hmem : F.Qk k ∈ D.target.carrier) :
    (k : ℝ) * (f : ℝ) ^ 2 < ((f : ℝ) - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧ k + 2 ≤ f := by
  have hle := F.line_mem_bound FC (by positivity) hmem
  have hlt := lt_of_le_of_ne hle (Qk_ne_exit F k)
  refine ⟨hlt, ?_⟩
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have : ((f : ℝ) - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((f : ℝ) - 1) * (f : ℝ) ^ 2 := by nlinarith
  have hk : (k : ℝ) < (f : ℝ) - 1 := by
    have := lt_trans hlt this
    exact lt_of_mul_lt_mul_right this hc0.le
  have : (k : ℝ) + 1 < f := by linarith
  have : k + 1 < f := by exact_mod_cast this
  omega

theorem Qk_interior (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F) (k : ℕ)
    (hmem : F.Qk k ∈ D.target.carrier) : F.Qk k ∈ interior D.target.carrier :=
  F.line_interior FC (by positivity) (Qk_lt F FC k hmem).1

theorem Vk_interior (F : HFrame D e f α β γ) (k : ℕ) (hk : 1 ≤ k)
    (hmem : F.Vk k ∈ D.target.carrier) : F.Vk k ∈ interior D.target.carrier := by
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by
    have : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by have := F.hef; omega)
    positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact F.hrint _ (mul_pos hk' hc0) (Vk_lt F k hmem)

theorem mem_of_present {N : ℕ} {D : CongruentDissection N} {S : Set Plane} {x : Plane}
    (h : Present D S) (hx : x ∈ S) : x ∈ D.target.carrier := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨q, hq⟩ := MarchInduction.mem_range_of_eq hi hx
  rw [← hq]; exact MarchInduction.pts_mem_target D.toDissection i q

/-- The near-side `c`-edge `[kV, (k+1)V]` of `L_k`. -/
theorem near_edge (F : HFrame D e f α β γ) (k : ℕ) (hL : Present D (F.Lc k)) :
    ∃ ε ∈ F.near, EdgeIs D ε (F.Vk k) (F.Vk (k + 1)) := by
  obtain ⟨i, hi⟩ := hL
  have hr : Set.range (D.tile i).pts = {F.Vk k, F.Vk (k + 1), F.Qk k} := hi
  obtain ⟨m0, hm0⟩ := MarchInduction.mem_range_of_eq hr (Set.mem_insert _ _)
  have hPA := F.hhP
  have hband : ∀ q, F.h ((D.tile i).pts q) ≤ F.h F.A := by
    intro q
    have : (D.tile i).pts q ∈ ({F.Vk k, F.Vk (k + 1), F.Qk k} : Set Plane) := hr ▸ ⟨q, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h <;> rw [h]
    · rw [F.h_Vk]
    · rw [F.h_Vk]
    · rw [F.h_Qk]; exact hPA.le
  rcases MarchInduction.vertex_data_of_range hr hm0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(i, m0), ?_, ?_⟩
    · show (i, m0) ∈ D.toDissection.lineChain F.h (F.h F.A)
      rw [Dissection.mem_lineChain]
      exact ⟨by simp only; rw [hm0, F.h_Vk], by simp only; rw [h1, F.h_Vk], hband⟩
    · show ({(D.tile i).pts m0, (D.tile i).pts (m0 + 1)} : Set Plane) = {F.Vk k, F.Vk (k + 1)}
      rw [hm0, h1]
  · refine ⟨(i, m0 + 2), ?_, ?_⟩
    · show (i, m0 + 2) ∈ D.toDissection.lineChain F.h (F.h F.A)
      rw [Dissection.mem_lineChain]
      refine ⟨by simp only; rw [h2, F.h_Vk], ?_, hband⟩
      simp only; rw [fin3_add_two_add_one, hm0, F.h_Vk]
    · show ({(D.tile i).pts (m0 + 2), (D.tile i).pts (m0 + 2 + 1)} : Set Plane)
        = {F.Vk k, F.Vk (k + 1)}
      rw [fin3_add_two_add_one, hm0, h2, Set.pair_comm]

/-- **Every chain point of the target is pierced** once `L₀, …, L_j` are tiles
(`HFrame.chain_point_pierced`, whose near `c`-word is supplied by the `L_i`). -/
theorem pierced_of (F : HFrame D e f α β γ) (j : ℕ) (hL : ∀ i ≤ j, Present D (F.Lc i))
    (hmem : F.Vk (j + 1) ∈ D.target.carrier) :
    TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) (F.Vk (j + 1)) := by
  have hkL := Vk_lt F (j + 1) hmem
  have := HFrame.chain_point_pierced F (j + 1) (by omega) hkL (fun i hi => by
    obtain ⟨ε, hε, hE⟩ := near_edge F i (hL i (by omega))
    refine ⟨ε, hε, ?_⟩
    have e1 : F.rpt ((i : ℝ) * (f : ℝ) ^ 2) = F.Vk i := rfl
    have e2 : F.rpt (((i : ℝ) + 1) * (f : ℝ) ^ 2) = F.Vk (i + 1) := by
      simp only [HFrame.rpt, HFrame.Vk]; push_cast; ring_nf
    rw [e1, e2]; exact hE)
  exact this


theorem small_step {b c η : ℝ} (hb : 0 < b) (hbc : b < c) (hη0 : 0 < η)
    (hη : η ≤ b * (c - b) / (2 * c)) : (1 : ℝ) * (b / c + η / b) < 1 := by
  have hc : 0 < c := by linarith
  have h1 : η / b ≤ (c - b) / (2 * c) := by
    rw [div_le_iff₀ hb]
    calc η ≤ b * (c - b) / (2 * c) := hη
      _ = (c - b) / (2 * c) * b := by ring
  have h2 : b / c + (c - b) / (2 * c) < 1 := by
    rw [div_add_div _ _ hc.ne' (by positivity), div_lt_one (by positivity)]; nlinarith
  rw [one_mul]; linarith

theorem small_pos {b c : ℝ} (hb : 0 < b) (hbc : b < c) : 0 < b * (c - b) / (2 * c) := by
  have hc : 0 < c := by linarith
  apply div_pos (mul_pos hb (by linarith)) (by positivity)

theorem step_point {X w u : Plane} {b c η : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    X + w + η • u = X + (1 : ℝ) • ((b / c) • ((c / b) • w) + (η / b) • (b • u)) := by
  rw [one_smul, smul_smul, smul_smul, show b / c * (c / b) = 1 by field_simp,
    show η / b * b = η by field_simp, one_smul]
  abel

/-- **Corner data in the apex frame** (at any point `x`): a `β` corner has flanks `{a, c}` and
opposite side `b`; an `α` corner has flanks `{b, c}` and opposite side `a`. -/
theorem corner_dataH (F : HFrame D e f α β γ) {i : Fin N} {m : Fin 3}
    {x U W : Plane} (hm : (D.tile i).pts m = x) (hUW : IsFlankPair (D.tile i) m x U W) :
    ((D.tile i).localAngle x = β →
      ((‖U‖ = (e : ℝ) * f ∧ ‖W‖ = (f : ℝ) ^ 2) ∨ (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (e : ℝ) * f)) ∧
      dist (x + U) (x + W) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
    ((D.tile i).localAngle x = α →
      ((‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2) ∨
        (‖U‖ = (f : ℝ) ^ 2 ∧ ‖W‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) ∧
      dist (x + U) (x + W) = (e : ℝ) * f) := by
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
    refine ⟨fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact ⟨Or.inl ⟨h1, h2⟩, h3⟩
      | exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
  · rw [hx, hx, hy, hy, dist_comm ((D.tile i).pts (m + 2)) ((D.tile i).pts (m + 1))]
    rcases hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    refine ⟨fun hg => ?_, fun hg => ?_⟩ <;>
    first
      | exact ⟨Or.inl ⟨h2, h1⟩, h3⟩
      | exact ⟨Or.inr ⟨h2, h1⟩, h3⟩
      | (exfalso; have h4 := (e1 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e2 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)
      | (exfalso; have h4 := (e3 h3).symm.trans hg
         first | linarith | exact hαβ h4 | exact hαβ h4.symm)

/-! ## §4 The two steps of the chain -/

/-- **V-step at the pierced chain point `(j+1)V`** (R4 Step 4, `C7`).  With `L_j` (`β` there) and
`K_j` (`γ`) present and the piercing edge (`π`), one `α`-tile remains, across `K_j`'s flank
`w = Q_{j+1} − (j+1)V`: either `L_{j+1} = T₂ + (j+1)(V − A)` (`b` on `w`), or the `L_b`-type tile
(`c` on `w`), `(j+1)V + {0, (c/b)·w, b·uR}`, whose interior contains `Q_{j+1} + ε·uR`, so no band
edge passes through `Q_{j+1}`.  (This is the case tree's "only `L_c` or `L_b` at `kV`".) -/
theorem vstep (F : HFrame D e f α β γ) (j : ℕ) (hLj : Present D (F.Lc j))
    (hKj : Present D (F.Kk j))
    (hpier : TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) (F.Vk (j + 1)))
    (hxint : F.Vk (j + 1) ∈ interior D.target.carrier) :
    Present D (F.Lc (j + 1)) ∨
      (Present D {F.Vk (j + 1),
          F.Vk (j + 1) + ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • (F.P - F.A),
          F.Vk (j + 1) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR} ∧
        ¬ TraceCovering.Straddled D.toDissection F.h (F.h F.P) (F.Qk (j + 1))) := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  have hAD := F.hAng
  obtain ⟨hab, hac, hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D hab hac hbc' F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  obtain ⟨iL, hiL⟩ := hLj
  obtain ⟨iK, hiK⟩ := hKj
  obtain ⟨ε, hεf, hstr⟩ := hpier
  have hiL' : Set.range (D.tile iL).pts = {F.Vk (j + 1), F.Vk j, F.Qk j} := by
    rw [hiL, HFrame.Lc, Set.insert_comm]
  have hiK' : Set.range (D.tile iK).pts = {F.Vk (j + 1), F.Qk (j + 1), F.Qk j} := by
    rw [hiK, HFrame.Kk, Set.pair_comm (F.Qk j)]
  have gL : (D.tile iL).localAngle (F.Vk (j + 1)) = β := by
    apply (hloc hiL').2.1
    rw [dist_comm, dist_eq_norm, F.Qk_sub_Vk]; exact F.hw_norm
  have gK : (D.tile iK).localAngle (F.Vk (j + 1)) = γ := by
    apply (hloc hiK').2.2
    rw [dist_eq_norm, F.Qk_succ_sub]; exact F.c_normR
  -- the piercing tile
  obtain ⟨hc2, hc0', hc1⟩ := openSeg_coords (D.tile ε.1) ε.2 hstr
  have hxb : F.Vk (j + 1) ∈ (D.tile ε.1).carrier := by
    rw [NearBaseVertex.mem_carrier_iff]; intro l
    rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'.le
    · exact hc1.le
    · exact hc2.ge
  have hbpos : ∀ l, l ≠ ε.2 + 2 → 0 < (D.tile ε.1).basis.coord l (F.Vk (j + 1)) := by
    intro l hl
    rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'
    · exact hc1
    · exact absurd rfl hl
  have hbnv : ∀ q, (D.tile ε.1).pts q ≠ F.Vk (j + 1) := fun q hq =>
    NearBaseVertex.vertex_not_edge _ q hq _ hbpos
  have hbang := localAngle_mem_pi_of_mem (D.tile ε.1) hxb hbnv
  -- counting: one each of `α`, `β`, `γ`, `π`
  obtain ⟨E1, E2⟩ := interior_card_eqs D hAD F.hM.hα' F.hM.hβ' F.hM.hγ' hxint
  have cB1 : 1 ≤ ({i | (D.tile i).localAngle (F.Vk (j + 1)) = β} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iL, mem_filter_of gL⟩
  have cC1 : 1 ≤ ({i | (D.tile i).localAngle (F.Vk (j + 1)) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iK, mem_filter_of gK⟩
  have hbπ : (D.tile ε.1).localAngle (F.Vk (j + 1)) = Real.pi := by
    rcases hbang with h | h
    · exfalso
      have : 1 ≤ ({i | (D.tile i).localAngle (F.Vk (j + 1)) = 2 * Real.pi} :
          Finset (Fin N)).card := Finset.card_pos.mpr ⟨ε.1, mem_filter_of h⟩
      omega
    · exact h
  have cP1 : 1 ≤ ({i | (D.tile i).localAngle (F.Vk (j + 1)) = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨ε.1, mem_filter_of hbπ⟩
  have cB : ({i | (D.tile i).localAngle (F.Vk (j + 1)) = β} : Finset (Fin N)).card = 1 := by omega
  have cC : ({i | (D.tile i).localAngle (F.Vk (j + 1)) = γ} : Finset (Fin N)).card = 1 := by omega
  have cP : ({i | (D.tile i).localAngle (F.Vk (j + 1)) = Real.pi} : Finset (Fin N)).card = 1 := by
    omega
  have cU : ({i | (D.tile i).localAngle (F.Vk (j + 1)) = 2 * Real.pi} :
      Finset (Fin N)).card = 0 := by omega
  -- the tile across `K_j`'s flank `w`
  obtain ⟨mK, hmK⟩ := MarchInduction.mem_range_of_eq hiK' (Set.mem_insert _ _)
  have hflK : IsFlankPair (D.tile iK) mK (F.Vk (j + 1)) (F.Qk (j + 1) - F.Vk (j + 1))
      (F.Qk j - F.Vk (j + 1)) := by
    rcases MarchInduction.vertex_data_of_range hiK' hmK with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  have hU0 : F.Qk (j + 1) - F.Vk (j + 1) = F.P - F.A := F.Qk_sub_Vk (j + 1)
  have hW0 : F.Qk j - F.Vk (j + 1) = (F.P - F.A) - ((f : ℝ) ^ 2) • F.uR := by
    rw [show F.Qk j - F.Vk (j + 1) = (F.Qk j - F.Vk j) - (F.Vk (j + 1) - F.Vk j) by abel,
      F.Qk_sub_Vk, F.Vk_succ_sub]
  have hgU0 : F.h (F.Qk (j + 1) - F.Vk (j + 1)) ≠ 0 := by rw [hU0]; exact F.hw_neg.ne
  obtain ⟨z, hzK, hxz, hcase⟩ := flank_neighbour_dissection D.toDissection hxint hmK hflK
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hJU, hside⟩ | ⟨m, hm0, hmpos, hcr, -⟩
  swap
  · -- edge case: `z` would be the piercing tile, with a second straight edge through `(j+1)V`
    exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ F.Vk (j + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m hmpos
    have hzπ : (D.tile z).localAngle (F.Vk (j + 1)) = Real.pi := by
      rcases localAngle_mem_pi_of_mem (D.tile z) hxz hznv with h | h
      · exfalso
        have : 1 ≤ ({i | (D.tile i).localAngle (F.Vk (j + 1)) = 2 * Real.pi} :
            Finset (Fin N)).card := Finset.card_pos.mpr ⟨z, mem_filter_of h⟩
        omega
      · exact h
    have hzb : z = ε.1 := eq_of_card_one cP (mem_filter_of hzπ) (mem_filter_of hbπ)
    subst hzb
    have hm : m = ε.2 + 2 := by
      by_contra hne
      have := hmpos (ε.2 + 2) (Ne.symm hne)
      linarith
    subst hm
    rw [fin3_add_two_add_two, fin3_add_two_add_one] at hcr
    have hε' : ε ∈ D.toDissection.lineChain (-F.h) (-(F.h F.A)) := hεf
    obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
    rw [LinearMap.neg_apply] at h0 h1
    have hne' : ∀ x : Fin 3, x ≠ x + 1 := by decide
    have hd0 := sub_ne_zero.mpr (pts_ne (D.tile ε.1) (hne' ε.2)).symm
    have hgd : F.h ((D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2) = 0 := by
      rw [map_sub]; linarith
    exact cross_ne_of_g F.h hd0 hgd hgU0 hcr
  -- vertex case: `z` is none of `L_j`, `K_j`, the piercing tile: the `α`-tile
  have hzL : z ≠ iL := by
    rintro rfl
    obtain ⟨mL, hmL⟩ := MarchInduction.mem_range_of_eq hiL' (Set.mem_insert _ _)
    have hmm : mL = mz := (D.tile z).indep.injective (hmL.trans hmz.symm)
    subst hmm
    have hflL : IsFlankPair (D.tile z) mL (F.Vk (j + 1)) (F.Vk j - F.Vk (j + 1))
        (F.Qk j - F.Vk (j + 1)) := by
      rcases MarchInduction.vertex_data_of_range hiL' hmL with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1], by rw [h2]⟩
      · right; exact ⟨by rw [h2], by rw [h1]⟩
    rcases ApexPlacement.flank_cases hflL hUW with ⟨hU', -⟩ | ⟨hU', -⟩
    · rw [hU'] at hJU
      have hVj : F.Vk j - F.Vk (j + 1) = (-((f : ℝ) ^ 2)) • F.uR := by
        rw [neg_smul, ← F.Vk_succ_sub j]; abel
      rw [hVj, hU0] at hJU
      have := congrArg (cross F.uR) hJU
      rw [cross_smul_right, cross_smul_right, cross_self', mul_zero, mul_zero] at this
      exact F.cross_uR_w this
    · rw [hU'] at hJU
      rw [hJU] at hside
      simp [cross_smul_left'] at hside
  have hzα : (D.tile z).localAngle (F.Vk (j + 1)) = α := by
    have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
    rw [hmz] at hang
    rcases hang with h | h | h
    · exact h
    · exact absurd (eq_of_card_one cB (mem_filter_of h) (mem_filter_of gL)) hzL
    · exact absurd (eq_of_card_one cC (mem_filter_of h) (mem_filter_of gK)) hzK
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).2 hzα
  have hU0n : ‖F.Qk (j + 1) - F.Vk (j + 1)‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hU0]; exact F.hw_norm
  have hSU : S * ‖U‖ = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [← hU0n, hJU, norm_smul, Real.norm_of_nonneg hS.le]
  have hid : cross (F.Qk (j + 1) - F.Vk (j + 1)) (((f : ℝ) ^ 2) • F.uR)
      = - cross (F.Qk (j + 1) - F.Vk (j + 1)) (F.Qk j - F.Vk (j + 1)) := by
    have : ((f : ℝ) ^ 2) • F.uR
        = (F.Qk (j + 1) - F.Vk (j + 1)) - (F.Qk j - F.Vk (j + 1)) := by
      rw [show (F.Qk (j + 1) - F.Vk (j + 1)) - (F.Qk j - F.Vk (j + 1)) = F.Qk (j + 1) - F.Qk j by
        abel, F.Qk_succ_sub]
    rw [this, cross_sub_right', cross_self', zero_sub]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` on `w`: the tile is `L_{j+1}`
    left
    have hS1 : S = 1 := by
      rw [h1] at hSU
      have : S * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 1 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) := by
        rw [hSU, one_mul]
      exact mul_right_cancel₀ hb0.ne' this
    have hUe : U = F.Qk (j + 1) - F.Vk (j + 1) := by rw [hJU, hS1, one_smul]
    have hUeq : F.Vk (j + 1) + U = F.Qk (j + 1) := by rw [hUe]; abel
    have hV2 : F.Vk (j + 2) = F.Vk (j + 1) + ((f : ℝ) ^ 2) • F.uR := by
      rw [← F.Vk_two_sub j]; abel
    have hZ : F.Vk (j + 1) + W = F.Vk (j + 2) := by
      apply third_vertex_cross (X := F.Vk (j + 1)) (Y := F.Qk (j + 1))
      · intro h; rw [← h, sub_self, norm_zero] at hU0n; linarith
      · rw [add_sub_cancel_left, hV2, add_sub_cancel_left, hid, mul_neg]; linarith
      · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2, hV2, dist_comm, dist_eq_norm,
          add_sub_cancel_left, F.c_normR]
      · have e1 : dist (F.Qk (j + 1)) (F.Vk (j + 1) + W) = (e : ℝ) * f := by
          rw [← hUeq]; exact hopp
        have e2 : dist (F.Qk (j + 1)) (F.Vk (j + 2)) = (e : ℝ) * f := by
          rw [dist_comm, dist_eq_norm, F.Vk_two_sub_Qk, F.hcw_norm]
        rw [e1, e2]
    refine ⟨z, ?_⟩
    rw [ApexPlacement.range_of_flank hmz hUW, hUeq, hZ, Set.pair_comm (F.Qk (j + 1))]
    rfl
  · -- `c` on `w`: the `L_b` tile; its interior reaches `ℓ` just past `Q_{j+1}`
    right
    have hUc : U = ((f : ℝ) ^ 2 / ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) • (F.P - F.A) := by
      rw [← hU0]; exact ApexPlacement.eq_smul_of_norms hS hJU hU0n h1 hb0
    rw [hJU] at hside hid
    simp only [cross_smul_left'] at hside hid
    have hpq : cross U W * cross U (F.Qk j - F.Vk (j + 1)) < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ (S * S) * (cross U W * cross U (F.Qk j - F.Vk (j + 1))) :=
        mul_nonneg (mul_pos hS hS).le hc
      nlinarith
    have hr : (f : ℝ) ^ 2 * cross U F.uR = - cross U (F.Qk j - F.Vk (j + 1)) := by
      rw [cross_smul_right] at hid
      have : S * ((f : ℝ) ^ 2 * cross U F.uR) = S * (- cross U (F.Qk j - F.Vk (j + 1))) := by
        rw [hid]; ring
      exact mul_left_cancel₀ hS.ne' this
    have hU0n' : U ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
    have hZ : F.Vk (j + 1) + W = F.Vk (j + 1) + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR := by
      apply third_vertex_cross (X := F.Vk (j + 1)) (Y := F.Vk (j + 1) + U)
      · intro h; apply hU0n'
        have := congrArg (fun p => p - F.Vk (j + 1)) h
        simpa using this.symm
      · rw [add_sub_cancel_left, add_sub_cancel_left, add_sub_cancel_left, cross_smul_right]
        have key : (f : ℝ) ^ 2 * (cross U W * (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * cross U F.uR))
            = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (cross U W * ((f : ℝ) ^ 2 * cross U F.uR)) := by ring
        rw [hr] at key
        have hpos : 0 < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
            * (cross U W * - cross U (F.Qk j - F.Vk (j + 1))) :=
          mul_pos hb0 (by rw [mul_neg]; linarith)
        rw [← key] at hpos
        exact pos_of_mul_pos_right hpos hc0.le
      · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2,
          dist_self_add_unit F.huR hb0.le]
      · rw [hopp, dist_eq_norm, add_sub_add_left_eq_sub, hUc]
        exact (refl_norm F.huR F.hw_norm hb0 ha0.le F.hcw_norm).symm
    have hW : W = ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR := add_left_cancel hZ
    refine ⟨⟨z, ?_⟩, ?_⟩
    · rw [ApexPlacement.range_of_flank hmz hUW, hUc, hW]
    -- points of `ℓ` just past `Q_{j+1}` are interior to `z`
    refine TraceCovering.not_straddled_of_near_interior (g := F.h) (d := F.h F.P) (f := F.h)
      (c := F.h F.P) (X := F.P) (u := F.uR) (fun _ => Iff.rfl) F.hh0 rfl F.hhuR F.uR_ne ?_
    intro δ hδ
    have hsp := small_pos hb0 hbc
    set η := min (δ / 2) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) ^ 2 - ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
      / (2 * (f : ℝ) ^ 2)) with hη
    have hη0 : 0 < η := lt_min (by linarith) hsp
    have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hxδ : |((j + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 + η - ((j + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2| < δ := by
      rw [add_sub_cancel_left, abs_of_pos hη0]; exact hηδ
    refine ⟨((j + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 + η, hxδ, z, ?_⟩
    have hint := open_dir_interior (D.tile z) mz hmz hUW (div_pos hb0 hc0) (div_pos hη0 hb0)
      one_pos (small_step hb0 hbc hη0 (min_le_right _ _))
    have e0 : F.P + (((j + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 + η) • F.uR
        = F.Vk (j + 1) + (F.P - F.A) + η • F.uR := by
      rw [HFrame.Vk]; module
    rw [e0, step_point hb0.ne' hc0.ne', ← hUc, ← hW]
    exact hint


/-- **Q-step at `Q_{j+1}`** (R4 Step 4).  With `K_j` (`α` there), `L_{j+1}` (`γ`) and a straight
band edge through `Q_{j+1}`, one `β`-tile remains, across `L_{j+1}`'s flank `Q_{j+1}(j+2)V`; with `a`
on that flank it is `K_{j+1}`; with `c`, its interior would contain `(j+2)V + ε·uR`, points of the
edge piercing `(j+2)V` — impossible. -/
theorem qstep (F : HFrame D e f α β γ) (j : ℕ) (hKp : Present D (F.Kk j))
    (hL : Present D (F.Lc (j + 1)))
    (hstr : TraceCovering.Straddled D.toDissection F.h (F.h F.P) (F.Qk (j + 1)))
    (hpier : TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) (F.Vk (j + 1 + 1)))
    (hxint : F.Qk (j + 1) ∈ interior D.target.carrier) : Present D (F.Kk (j + 1)) := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have ha0 : (0 : ℝ) < (e : ℝ) * f := by nlinarith
  have hac : (e : ℝ) * f < (f : ℝ) ^ 2 := by nlinarith
  have hAD := F.hAng
  obtain ⟨hab, hac', hbc'⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have hloc := fun {i : Fin N} {P Q R : Plane} (hr : Set.range (D.tile i).pts = {P, Q, R}) =>
    localAngle_of_rangeE D hab hac' hbc' F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ' F.hM.hγ' hr
  obtain ⟨iA, hiA⟩ := hKp
  obtain ⟨iC, hiC⟩ := hL
  obtain ⟨ε, hεb, hstr'⟩ := hstr
  have hiA' : Set.range (D.tile iA).pts = {F.Qk (j + 1), F.Vk (j + 1), F.Qk j} := by
    rw [hiA, HFrame.Kk, Set.pair_comm (F.Qk j), Set.insert_comm]
  have hiC' : Set.range (D.tile iC).pts = {F.Qk (j + 1), F.Vk (j + 1 + 1), F.Vk (j + 1)} := by
    rw [hiC, HFrame.Lc, Set.pair_comm (F.Vk (j + 1 + 1)), Set.insert_comm,
      Set.pair_comm (F.Vk (j + 1))]
  have gA : (D.tile iA).localAngle (F.Qk (j + 1)) = α := by
    apply (hloc hiA').1
    rw [dist_eq_norm, F.Vk_succ_sub_Qk]; exact F.hcw_norm
  have gC : (D.tile iC).localAngle (F.Qk (j + 1)) = γ := by
    apply (hloc hiC').2.2
    rw [dist_eq_norm, F.Vk_succ_sub]; exact F.c_normR
  -- the band tile
  obtain ⟨hc2, hc0', hc1⟩ := openSeg_coords (D.tile ε.1) ε.2 hstr'
  have hxb : F.Qk (j + 1) ∈ (D.tile ε.1).carrier := by
    rw [NearBaseVertex.mem_carrier_iff]; intro l
    rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'.le
    · exact hc1.le
    · exact hc2.ge
  have hbpos : ∀ l, l ≠ ε.2 + 2 → 0 < (D.tile ε.1).basis.coord l (F.Qk (j + 1)) := by
    intro l hl
    rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'
    · exact hc1
    · exact absurd rfl hl
  have hbnv : ∀ q, (D.tile ε.1).pts q ≠ F.Qk (j + 1) := fun q hq =>
    NearBaseVertex.vertex_not_edge _ q hq _ hbpos
  have hbang := localAngle_mem_pi_of_mem (D.tile ε.1) hxb hbnv
  obtain ⟨E1, E2⟩ := interior_card_eqs D hAD F.hM.hα' F.hM.hβ' F.hM.hγ' hxint
  have cA1 : 1 ≤ ({i | (D.tile i).localAngle (F.Qk (j + 1)) = α} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iA, mem_filter_of gA⟩
  have cC1 : 1 ≤ ({i | (D.tile i).localAngle (F.Qk (j + 1)) = γ} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨iC, mem_filter_of gC⟩
  have hbπ : (D.tile ε.1).localAngle (F.Qk (j + 1)) = Real.pi := by
    rcases hbang with h | h
    · exfalso
      have : 1 ≤ ({i | (D.tile i).localAngle (F.Qk (j + 1)) = 2 * Real.pi} :
          Finset (Fin N)).card := Finset.card_pos.mpr ⟨ε.1, mem_filter_of h⟩
      omega
    · exact h
  have cP1 : 1 ≤ ({i | (D.tile i).localAngle (F.Qk (j + 1)) = Real.pi} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨ε.1, mem_filter_of hbπ⟩
  have cA : ({i | (D.tile i).localAngle (F.Qk (j + 1)) = α} : Finset (Fin N)).card = 1 := by omega
  have cC : ({i | (D.tile i).localAngle (F.Qk (j + 1)) = γ} : Finset (Fin N)).card = 1 := by omega
  have cP : ({i | (D.tile i).localAngle (F.Qk (j + 1)) = Real.pi} : Finset (Fin N)).card = 1 := by
    omega
  have cU : ({i | (D.tile i).localAngle (F.Qk (j + 1)) = 2 * Real.pi} :
      Finset (Fin N)).card = 0 := by omega
  -- the tile across `L_{j+1}`'s flank `Q_{j+1}(j+2)V`
  obtain ⟨mC, hmC⟩ := MarchInduction.mem_range_of_eq hiC' (Set.mem_insert _ _)
  have hflC : IsFlankPair (D.tile iC) mC (F.Qk (j + 1)) (F.Vk (j + 1 + 1) - F.Qk (j + 1))
      (F.Vk (j + 1) - F.Qk (j + 1)) := by
    rcases MarchInduction.vertex_data_of_range hiC' hmC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [h1], by rw [h2]⟩
    · right; exact ⟨by rw [h2], by rw [h1]⟩
  have hU0 : F.Vk (j + 1 + 1) - F.Qk (j + 1) = ((f : ℝ) ^ 2) • F.uR - (F.P - F.A) :=
    F.Vk_succ_sub_Qk (j + 1)
  have hW0 : F.Vk (j + 1) - F.Qk (j + 1) = -(F.P - F.A) := by
    rw [show F.Vk (j + 1) - F.Qk (j + 1) = -(F.Qk (j + 1) - F.Vk (j + 1)) by abel, F.Qk_sub_Vk]
  have hgU0 : F.h (F.Vk (j + 1 + 1) - F.Qk (j + 1)) ≠ 0 := by
    rw [hU0, map_sub, map_smul, F.hhuR, smul_zero, zero_sub, neg_ne_zero]
    exact F.hw_neg.ne
  obtain ⟨z, hzC, hxz, hcase⟩ := flank_neighbour_dissection D.toDissection hxint hmC hflC
  rcases hcase with ⟨mz, hmz, U, W, hUW, S, hS, hJU, hside⟩ | ⟨m, hm0, hmpos, hcr, -⟩
  swap
  · exfalso
    have hznv : ∀ q, (D.tile z).pts q ≠ F.Qk (j + 1) := fun q hq =>
      NearBaseVertex.vertex_not_edge _ q hq m hmpos
    have hzπ : (D.tile z).localAngle (F.Qk (j + 1)) = Real.pi := by
      rcases localAngle_mem_pi_of_mem (D.tile z) hxz hznv with h | h
      · exfalso
        have : 1 ≤ ({i | (D.tile i).localAngle (F.Qk (j + 1)) = 2 * Real.pi} :
            Finset (Fin N)).card := Finset.card_pos.mpr ⟨z, mem_filter_of h⟩
        omega
      · exact h
    have hzb : z = ε.1 := eq_of_card_one cP (mem_filter_of hzπ) (mem_filter_of hbπ)
    subst hzb
    have hm : m = ε.2 + 2 := by
      by_contra hne
      have := hmpos (ε.2 + 2) (Ne.symm hne)
      linarith
    subst hm
    rw [fin3_add_two_add_two, fin3_add_two_add_one] at hcr
    have hε' : ε ∈ D.toDissection.lineChain F.h (F.h F.P) := hεb
    obtain ⟨h0, h1, -⟩ := Dissection.mem_lineChain.mp hε'
    have hne' : ∀ x : Fin 3, x ≠ x + 1 := by decide
    have hd0 := sub_ne_zero.mpr (pts_ne (D.tile ε.1) (hne' ε.2)).symm
    have hgd : F.h ((D.tile ε.1).pts (ε.2 + 1) - (D.tile ε.1).pts ε.2) = 0 := by
      rw [map_sub]; linarith
    exact cross_ne_of_g F.h hd0 hgd hgU0 hcr
  have hzA : z ≠ iA := by
    rintro rfl
    obtain ⟨mA, hmA⟩ := MarchInduction.mem_range_of_eq hiA' (Set.mem_insert _ _)
    have hmm : mA = mz := (D.tile z).indep.injective (hmA.trans hmz.symm)
    subst hmm
    have hflA : IsFlankPair (D.tile z) mA (F.Qk (j + 1)) (F.Vk (j + 1) - F.Qk (j + 1))
        (F.Qk j - F.Qk (j + 1)) := by
      rcases MarchInduction.vertex_data_of_range hiA' hmA with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨by rw [h1], by rw [h2]⟩
      · right; exact ⟨by rw [h2], by rw [h1]⟩
    rcases ApexPlacement.flank_cases hflA hUW with ⟨hU', -⟩ | ⟨hU', -⟩
    · rw [hU'] at hJU
      rw [hJU] at hside
      simp [cross_smul_left'] at hside
    · rw [hU'] at hJU
      have hQj : F.Qk j - F.Qk (j + 1) = (-((f : ℝ) ^ 2)) • F.uR := by
        rw [neg_smul, ← F.Qk_succ_sub j]; abel
      rw [hQj, hU0] at hJU
      have := congrArg (cross F.uR) hJU
      rw [cross_sub_right', cross_smul_right, cross_self', mul_zero, zero_sub,
        cross_smul_right, cross_smul_right, cross_self', mul_zero, mul_zero, neg_eq_zero] at this
      exact F.cross_uR_w this
  have hzβ : (D.tile z).localAngle (F.Qk (j + 1)) = β := by
    have hang := localAngle_at_own_vertex_mem D α β γ F.hM.hα' F.hM.hβ' F.hM.hγ' z mz
    rw [hmz] at hang
    rcases hang with h | h | h
    · exact absurd (eq_of_card_one cA (mem_filter_of h) (mem_filter_of gA)) hzA
    · exact h
    · exact absurd (eq_of_card_one cC (mem_filter_of h) (mem_filter_of gC)) hzC
  obtain ⟨hn, hopp⟩ := (corner_dataH F hmz hUW).1 hzβ
  have hU0n : ‖F.Vk (j + 1 + 1) - F.Qk (j + 1)‖ = (e : ℝ) * f := by rw [hU0]; exact F.hcw_norm
  have hSU : S * ‖U‖ = (e : ℝ) * f := by
    rw [← hU0n, hJU, norm_smul, Real.norm_of_nonneg hS.le]
  have hid : cross (F.Vk (j + 1 + 1) - F.Qk (j + 1)) (((f : ℝ) ^ 2) • F.uR)
      = - cross (F.Vk (j + 1 + 1) - F.Qk (j + 1)) (F.Vk (j + 1) - F.Qk (j + 1)) := by
    have : ((f : ℝ) ^ 2) • F.uR
        = (F.Vk (j + 1 + 1) - F.Qk (j + 1)) - (F.Vk (j + 1) - F.Qk (j + 1)) := by
      rw [hU0, hW0]; abel
    rw [this, cross_sub_right', cross_self', zero_sub]
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `a` on the flank: the tile is `K_{j+1}`
    have hS1 : S = 1 := by
      rw [h1] at hSU
      have : S * ((e : ℝ) * f) = 1 * ((e : ℝ) * f) := by rw [hSU, one_mul]
      exact mul_right_cancel₀ ha0.ne' this
    have hUe : U = F.Vk (j + 1 + 1) - F.Qk (j + 1) := by rw [hJU, hS1, one_smul]
    have hUeq : F.Qk (j + 1) + U = F.Vk (j + 1 + 1) := by rw [hUe]; abel
    have hQ2 : F.Qk (j + 1 + 1) = F.Qk (j + 1) + ((f : ℝ) ^ 2) • F.uR := by
      rw [← F.Qk_succ_sub (j + 1)]; abel
    have hZ : F.Qk (j + 1) + W = F.Qk (j + 1 + 1) := by
      apply third_vertex_cross (X := F.Qk (j + 1)) (Y := F.Vk (j + 1 + 1))
      · intro h; rw [← h, sub_self, norm_zero] at hU0n; linarith
      · rw [add_sub_cancel_left, hQ2, add_sub_cancel_left, hid, mul_neg]; linarith
      · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2, hQ2, dist_comm, dist_eq_norm,
          add_sub_cancel_left, F.c_normR]
      · have e1 : dist (F.Vk (j + 1 + 1)) (F.Qk (j + 1) + W) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
          rw [← hUeq]; exact hopp
        have e2 : dist (F.Vk (j + 1 + 1)) (F.Qk (j + 1 + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
          rw [dist_comm, dist_eq_norm, F.Qk_sub_Vk]; exact F.hw_norm
        rw [e1, e2]
    refine ⟨z, ?_⟩
    rw [ApexPlacement.range_of_flank hmz hUW, hUeq, hZ, Set.insert_comm]
    rfl
  · -- `c` on the flank: its interior would meet the edge piercing `(j+2)V`
    exfalso
    have hUc : U = ((f : ℝ) ^ 2 / ((e : ℝ) * f)) • (F.Vk (j + 1 + 1) - F.Qk (j + 1)) :=
      ApexPlacement.eq_smul_of_norms hS hJU hU0n h1 ha0
    rw [hJU] at hside hid
    simp only [cross_smul_left'] at hside hid
    have hpq : cross U W * cross U (F.Vk (j + 1) - F.Qk (j + 1)) < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ (S * S) * (cross U W * cross U (F.Vk (j + 1) - F.Qk (j + 1))) :=
        mul_nonneg (mul_pos hS hS).le hc
      nlinarith
    have hr : (f : ℝ) ^ 2 * cross U F.uR = - cross U (F.Vk (j + 1) - F.Qk (j + 1)) := by
      rw [cross_smul_right] at hid
      have : S * ((f : ℝ) ^ 2 * cross U F.uR) = S * (- cross U (F.Vk (j + 1) - F.Qk (j + 1))) := by
        rw [hid]; ring
      exact mul_left_cancel₀ hS.ne' this
    have hU0n' : U ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
    have hcw : ‖((f : ℝ) ^ 2) • F.uR - (F.Vk (j + 1 + 1) - F.Qk (j + 1))‖
        = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
      rw [hU0, show ((f : ℝ) ^ 2) • F.uR - (((f : ℝ) ^ 2) • F.uR - (F.P - F.A)) = F.P - F.A by abel]
      exact F.hw_norm
    have hZ : F.Qk (j + 1) + W = F.Qk (j + 1) + ((e : ℝ) * f) • F.uR := by
      apply third_vertex_cross (X := F.Qk (j + 1)) (Y := F.Qk (j + 1) + U)
      · intro h; apply hU0n'
        have := congrArg (fun p => p - F.Qk (j + 1)) h
        simpa using this.symm
      · rw [add_sub_cancel_left, add_sub_cancel_left, add_sub_cancel_left, cross_smul_right]
        have key : (f : ℝ) ^ 2 * (cross U W * (((e : ℝ) * f) * cross U F.uR))
            = ((e : ℝ) * f) * (cross U W * ((f : ℝ) ^ 2 * cross U F.uR)) := by ring
        rw [hr] at key
        have hpos : 0 < ((e : ℝ) * f) * (cross U W * - cross U (F.Vk (j + 1) - F.Qk (j + 1))) :=
          mul_pos ha0 (by rw [mul_neg]; linarith)
        rw [← key] at hpos
        exact pos_of_mul_pos_right hpos hc0.le
      · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, h2,
          dist_self_add_unit F.huR ha0.le]
      · rw [hopp, dist_eq_norm, add_sub_add_left_eq_sub, hUc]
        exact (refl_norm F.huR hU0n ha0 hb0.le hcw).symm
    have hW : W = ((e : ℝ) * f) • F.uR := add_left_cancel hZ
    apply TraceCovering.not_straddled_of_near_interior (g := -F.h) (d := -(F.h F.A)) (f := -F.h)
      (c := -(F.h F.A)) (X := F.A) (u := F.uR) (fun _ => Iff.rfl) (neg_ne_zero.mpr F.hh0) rfl
      (by rw [LinearMap.neg_apply, F.hhuR, neg_zero]) F.uR_ne ?_ hpier
    intro δ hδ
    have hsp := small_pos ha0 hac
    set η := min (δ / 2) (((e : ℝ) * f) * ((f : ℝ) ^ 2 - (e : ℝ) * f) / (2 * (f : ℝ) ^ 2)) with hη
    have hη0 : 0 < η := lt_min (by linarith) hsp
    have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hxδ : |((j + 1 + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 + η - ((j + 1 + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2| < δ := by
      rw [add_sub_cancel_left, abs_of_pos hη0]; exact hηδ
    refine ⟨((j + 1 + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 + η, hxδ, z, ?_⟩
    have hint := open_dir_interior (D.tile z) mz hmz hUW (div_pos ha0 hc0) (div_pos hη0 ha0)
      one_pos (small_step ha0 hac hη0 (min_le_right _ _))
    have e0 : F.A + (((j + 1 + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 + η) • F.uR
        = F.Qk (j + 1) + (F.Vk (j + 1 + 1) - F.Qk (j + 1)) + η • F.uR := by
      rw [add_sub_cancel, HFrame.Vk]; module
    rw [e0, step_point ha0.ne' hc0.ne', ← hUc, ← hW]
    exact hint

/-- **Chain end.**  If the band covering of `ℓ` from `P′` starts with a `b`-edge, `K₀, …, K_k` are
tiles and `Q_{k+1}` is a band junction, then the band edges on `[P′, Q_{k+1}]` (a wall: the `c`-edges
of the `K_i`) are whole and total `(k+1)·c` (`TraceCovering.wall_sum`) with a `b` among them, and
`k + 1 ≤ f − 2 < f` (`Qk_lt`): `Inflation.c_side_no_b` forbids it. -/
theorem band_end (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K)
    (hb : ∃ ε ∈ F.band, EdgeIs D ε F.P (F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR))
    (k : ℕ) (hKs : ∀ i ≤ k, Present D (F.Kk i))
    (hjunc : ¬ TraceCovering.Straddled D.toDissection F.h (F.h F.P) (F.Qk (k + 1))) : False := by
  classical
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hbc : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith
  have hQ : F.Qk (k + 1) ∈ D.target.carrier :=
    mem_of_present (hKs k le_rfl) (by simp [HFrame.Kk])
  obtain ⟨hlt, hk2⟩ := Qk_lt F FC (k + 1) hQ
  set t : ℝ := ((k + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hct : (f : ℝ) ^ 2 ≤ t := by
    rw [ht]; push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hint : ∀ x ∈ Set.Ioo 0 t, F.P + x • F.uR ∈ interior D.target.carrier :=
    fun x hx => F.line_interior FC hx.1.le (lt_trans hx.2 hlt)
  have hwall : ∀ x ∈ Set.Ioo 0 t, ∀ i, F.P + x • F.uR ∉ interior (D.tile i).carrier := by
    intro x hx i
    set q := ⌊x / (f : ℝ) ^ 2⌋₊ with hq
    have hq0 : 0 ≤ x / (f : ℝ) ^ 2 := div_nonneg hx.1.le hc0.le
    have hq1 : (q : ℝ) ≤ x / (f : ℝ) ^ 2 := Nat.floor_le hq0
    have hq2 : x / (f : ℝ) ^ 2 < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hqx : (q : ℝ) * (f : ℝ) ^ 2 ≤ x := by rwa [le_div_iff₀ hc0] at hq1
    have hxq : x < ((q : ℝ) + 1) * (f : ℝ) ^ 2 := by rwa [div_lt_iff₀ hc0] at hq2
    have hqk : q ≤ k := by
      have h1 : (q : ℝ) * (f : ℝ) ^ 2 < ((k + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 := lt_of_le_of_lt hqx hx.2
      have h2 : q < k + 1 := by exact_mod_cast lt_of_mul_lt_mul_right h1 hc0.le
      omega
    obtain ⟨iz, hiz⟩ := hKs q hqk
    obtain ⟨k0, hk0⟩ := MarchInduction.mem_range_of_eq hiz
      (show F.Qk q ∈ F.Kk q by simp [HFrame.Kk])
    obtain ⟨k1, hk1'⟩ := MarchInduction.mem_range_of_eq hiz
      (show F.Qk (q + 1) ∈ F.Kk q by simp [HFrame.Kk])
    have hQne : F.Qk q ≠ F.Qk (q + 1) := by
      intro h
      have := congrArg (fun p => p - F.Qk q) h
      simp only [sub_self] at this
      rw [F.Qk_succ_sub] at this
      have h3 := congrArg norm this
      rw [norm_zero, F.c_normR] at h3
      linarith
    have hkne : k0 ≠ k1 := by rintro rfl; exact hQne (hk0.symm.trans hk1')
    obtain ⟨m, hm⟩ := (D.tile iz).pair_eq_edge hkne
    have hmem : F.P + x • F.uR ∈ (D.tile iz).edge m := by
      rw [← hm, hk0, hk1', HFrame.Qk, HFrame.Qk, TraceCovering.segment_param]
      refine ⟨x, ⟨?_, ?_⟩, rfl⟩
      · push_cast; exact le_trans (min_le_left _ _) hqx
      · push_cast; exact le_trans hxq.le (le_max_right _ _)
    exact D.toDissection.edge_point_not_interior hmem i
  have hs : ¬ TraceCovering.Straddled D.toDissection F.h (F.h F.P) (F.P + (0 : ℝ) • F.uR) := by
    rintro ⟨ε, -, hstr⟩
    rw [zero_smul, add_zero] at hstr
    obtain ⟨hc2, hc0', hc1⟩ := openSeg_coords (D.tile ε.1) ε.2 hstr
    have hPm : F.P ∈ (D.tile ε.1).carrier := by
      rw [NearBaseVertex.mem_carrier_iff]; intro l
      rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
      · exact hc0'.le
      · exact hc1.le
      · exact hc2.ge
    obtain ⟨q, hq⟩ := pprime_vertex_of_mem F hK ε.1 hPm
    refine NearBaseVertex.vertex_not_edge _ q hq (ε.2 + 2) (fun l hl => ?_)
    rcases fin3_cases3 ε.2 l with rfl | rfl | rfl
    · exact hc0'
    · exact hc1
    · exact absurd rfl hl
  have hsum := TraceCovering.wall_sum (D := D.toDissection) (f := F.h) (c := F.h F.P) F.hh0
    (fun _ => Iff.rfl) F.hh0 rfl F.hhuR F.huR ht0 hint hwall hs hjunc
  -- the first band edge, a `b`
  obtain ⟨ε0, hε0, hE0⟩ := hb
  have hE0' := Set.pair_eq_pair_iff.mp hE0
  have hSeg : ∀ y, y = F.P ∨ y = F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR →
      y ∈ segment ℝ (F.P + (0 : ℝ) • F.uR) (F.P + t • F.uR) := by
    rintro y (rfl | rfl)
    · convert left_mem_segment ℝ (F.P + (0 : ℝ) • F.uR) (F.P + t • F.uR) using 1
      rw [zero_smul, add_zero]
    · rw [TraceCovering.segment_param, min_eq_left ht0, max_eq_right ht0]
      exact ⟨_, ⟨hb0.le, by linarith⟩, rfl⟩
  have hin : (D.tile ε0.1).edge ε0.2 ⊆ segment ℝ (F.P + (0 : ℝ) • F.uR) (F.P + t • F.uR) := by
    rw [Tri.edge]
    rcases hE0' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      exact (convex_segment _ _).segment_subset (hSeg _ (by simp)) (hSeg _ (by simp))
  have hdM : dist ((D.tile ε0.1).pts ε0.2) ((D.tile ε0.1).pts (ε0.2 + 1))
      = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have hdb : dist F.P (F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
      dist_self_add_unit F.huR hb0.le
    rcases hE0' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hdb
    · rw [dist_comm]; exact hdb
  set s := (D.toDissection.lineChain F.h (F.h F.P)).filter
    (fun ε => (D.tile ε.1).edge ε.2 ⊆ segment ℝ (F.P + (0 : ℝ) • F.uR) (F.P + t • F.uR))
    with hs_def
  have hmemS : ε0 ∈ s := Finset.mem_filter.mpr ⟨hε0, hin⟩
  rw [← Finset.add_sum_erase s _ hmemS] at hsum
  obtain ⟨P', Q', R', hPQR, -⟩ := sum_three_values (s.erase ε0)
    (fun ε => dist ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)
    (fun ε _ => MirrorStripR2Glue.edge_len_mem D F.hM.hs0 F.hM.hs1 F.hM.hs2 ε.1 ε.2)
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left (by have := F.hef; omega) 2
  have hreal : ((P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 : ℕ) : ℝ)
      = (((k + 1) * f ^ 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hee]
    simp only at hsum hdM
    rw [hdM] at hsum
    rw [ht] at hsum
    push_cast at hsum
    linarith
  have hnat : P' * (e * f) + (Q' + 1) * (f ^ 2 - e ^ 2) + R' * f ^ 2 = (k + 1) * f ^ 2 := by
    exact_mod_cast hreal
  have := Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) (k + 1) P' (Q' + 1) R'
    (by have := F.he; omega) (by have := F.hef; omega) F.hco (Nat.sub_add_cancel hee)
    (by omega) hnat
  omega

/-- **R4 (b), `HalfTurnR3R4Glue.t2pprime_forced`, PROVED.**  In branch (H) of an `m = 1`
dissection (apex frame with cone coordinates), `T₂ + P′` is a tile, presenting `α` at `P′`.  By
`pprime_order'` the first band edge on `ℓ⁺` is `b` or `c`, a `c` being `T₂ + P′`; if it were `b`, the
chain `L₀ = T₂, K₀ = K, L₁, K₁, …` is forced step by step (`vstep`, `qstep`, every chain point
pierced: `pierced_of`) until it ends at a band junction `Q_k`, `k ≤ f − 2` (`band_end`), or runs off
`ℓ` (`Qk_lt`). -/
theorem t2pprime_forced' (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K) :
    ∃ i, Set.range (D.tile i).pts = F.T2P ∧ (D.tile i).localAngle F.P = α := by
  classical
  obtain ⟨hab, hac, hbc⟩ := sides_distinct F.hco F.he (by have := F.hef; omega)
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast F.he
  have hefR : (e : ℝ) + 2 ≤ f := by exact_mod_cast F.hef
  have hc0 : (0 : ℝ) < (f : ℝ) ^ 2 := by nlinarith
  obtain ⟨ε, hε, Lε, hLε, hE, hT⟩ := pprime_order' F hK
  have hT2P : Present D F.T2P := by
    rcases hLε with hLb | hLc
    · exfalso
      rw [hLb] at hE
      have hb : ∃ ε ∈ F.band, EdgeIs D ε F.P (F.P + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) • F.uR) :=
        ⟨ε, hε, hE⟩
      have hL0 : Present D (F.Lc 0) := by
        obtain ⟨i2, h2⟩ := F.hT2
        exact ⟨i2, by rw [h2, HFrame.Lc, F.Vk_zero, F.Vk_one, F.Qk_zero]⟩
      have hQ1 : F.Qk 1 = F.V + F.P - F.A := by
        simp only [HFrame.Qk, Nat.cast_one, one_mul]; rw [F.hV]; abel
      have hK0 : Present D (F.Kk 0) := by
        obtain ⟨k0, hk0⟩ := hK
        refine ⟨k0, ?_⟩
        rw [hk0, HFrame.K, HFrame.Kk, zero_add, F.Vk_one, F.Qk_zero, hQ1]
      let St : ℕ → Prop := fun j => (∀ i ≤ j, Present D (F.Lc i)) ∧
        (∀ i < j, Present D (F.Kk i)) ∧
        TraceCovering.Straddled D.toDissection F.h (F.h F.P) (F.Qk j)
      -- the base: `L₁` and a straddle at `Q₁`
      have hst1 : St 1 := by
        have hVmem : F.Vk (0 + 1) ∈ D.target.carrier := by
          rw [zero_add, F.Vk_one]
          obtain ⟨i2, h2⟩ := F.hT2
          exact mem_of_present ⟨i2, h2⟩ (by simp)
        have hpV : TraceCovering.Straddled D.toDissection (-F.h) (-(F.h F.A)) (F.Vk (0 + 1)) := by
          rw [zero_add, F.Vk_one]; exact HFrame.V_pierced F
        rcases vstep F 0 hL0 hK0 hpV (Vk_interior F (0 + 1) le_rfl hVmem) with hL1 | hn
        · refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
          · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
            · exact hL0
            · exact hL1
          · have : i = 0 := by omega
            subst this; exact hK0
          · by_contra hn
            exact band_end F FC hK hb 0 (fun i hi => by
              have : i = 0 := by omega
              subst this; exact hK0) hn
        · exact (band_end F FC hK hb 0 (fun i hi => by
            have : i = 0 := by omega
            subst this; exact hK0) hn.2).elim
      -- the step
      have hstep : ∀ j', St (j' + 1) → St (j' + 1 + 1) := by
        intro j' ⟨hLs, hKs, hstrj⟩
        have hLj : Present D (F.Lc (j' + 1)) := hLs (j' + 1) le_rfl
        have hV2 : F.Vk (j' + 1 + 1) ∈ D.target.carrier :=
          mem_of_present hLj (by simp [HFrame.Lc])
        have hpier := pierced_of F (j' + 1) hLs hV2
        have hQmem : F.Qk (j' + 1) ∈ D.target.carrier :=
          mem_of_present hLj (by simp [HFrame.Lc])
        have hK1 := qstep F j' (hKs j' (by omega)) hLj hstrj hpier
          (Qk_interior F FC (j' + 1) hQmem)
        have hKs' : ∀ i ≤ j' + 1, Present D (F.Kk i) := fun i hi => by
          rcases Nat.lt_or_ge i (j' + 1) with h | h
          · exact hKs i h
          · have : i = j' + 1 := by omega
            subst this; exact hK1
        rcases vstep F (j' + 1) hLj hK1 hpier (Vk_interior F (j' + 1 + 1) (by omega) hV2) with
          hL2 | hn
        · refine ⟨fun i hi => ?_, fun i hi => hKs' i (by omega), ?_⟩
          · rcases Nat.lt_or_ge i (j' + 1 + 1) with h | h
            · exact hLs i (by omega)
            · have : i = j' + 1 + 1 := by omega
              subst this; exact hL2
          · by_contra hn
            exact band_end F FC hK hb (j' + 1) hKs' hn
        · exact (band_end F FC hK hb (j' + 1) hKs' hn.2).elim
      have hall : ∀ n, St (n + 1) := by
        intro n
        induction n with
        | zero => exact hst1
        | succ n ih => exact hstep n ih
      obtain ⟨hLs, -, -⟩ := hall (f - 2)
      have hmem : F.Qk (f - 2 + 1) ∈ D.target.carrier :=
        mem_of_present (hLs (f - 2 + 1) le_rfl) (by simp [HFrame.Lc])
      have := (Qk_lt F FC (f - 2 + 1) hmem).2
      have := F.hef
      omega
    · exact hT hLc
  obtain ⟨i, hi⟩ := hT2P
  refine ⟨i, hi, ?_⟩
  have hr : Set.range (D.tile i).pts = {F.P, F.V + F.P - F.A, F.P + F.P - F.A} := hi
  apply (localAngle_of_rangeE D hab hac hbc F.hM.hs0 F.hM.hs1 F.hM.hs2 F.hM.hα' F.hM.hβ'
    F.hM.hγ' hr).1
  rw [dist_eq_norm, show F.V + F.P - F.A - (F.P + F.P - F.A) = F.V - F.P by abel, ← dist_eq_norm]
  exact F.hVP

/-- **R4 (b) for EVERY real `m = 1` dissection**: `K` and `T₂ + P′` are tiles (the latter `α` at
`P′`), in the dissection's apex frame. -/
theorem t2pprime_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, Present D F.K ∧
      ∃ i, Set.range (D.tile i).pts = F.T2P ∧ (D.tile i).localAngle F.P = α := by
  obtain ⟨F, FC, hK⟩ := K_present_real h
  exact ⟨F, hK, t2pprime_forced' F FC hK⟩


/-- **R4 (c): the figure at `P′` in (H) is `{2α, 2β, 2γ}`, no straight angle — PROVED** (the
assembly `HalfTurnR3R4Glue.r4_figure_at_pprime` with its `t2pprime_forced` input discharged). -/
theorem r4_figure_at_pprime' (F : HFrame D e f α β γ) (FC : ApexPlacement.FrameCoords F)
    (hK : Present D F.K) :
    ({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle F.P = Real.pi} : Finset (Fin N)).card = 0 := by
  classical
  obtain ⟨i2, i3, k, h23, h2, h3, hk⟩ := HFrame.corners_at_pprime F hK
  obtain ⟨j, -, hj⟩ := t2pprime_forced' F FC hK
  obtain ⟨E1, E2⟩ := interior_card_eqs D F.hAng F.hM.hα' F.hM.hβ' F.hM.hγ' F.hPint
  have hA1 : 1 ≤ ({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨j, mem_filter_of hj⟩
  have hB1 : 1 ≤ ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)).card :=
    Finset.card_pos.mpr ⟨k, mem_filter_of hk⟩
  have hC2 : 2 ≤ ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card := by
    have hsub : ({i2, i3} : Finset (Fin N)) ⊆
        ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter_of h2
      · exact mem_filter_of h3
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair h23] at this
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **R4 (c) for EVERY real `m = 1` dissection.** -/
theorem r4_figure_real {k : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ k) :
    ∃ F : HFrame D e f α β γ, Present D F.K ∧
      ({i | (D.tile i).localAngle F.P = α} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle F.P = β} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle F.P = γ} : Finset (Fin N)).card = 2 ∧
      ({i | (D.tile i).localAngle F.P = Real.pi} : Finset (Fin N)).card = 0 := by
  obtain ⟨F, FC, hK⟩ := K_present_real h
  exact ⟨F, hK, r4_figure_at_pprime' F FC hK⟩

end Erdos634.Draft.HalfTurnR4Real

#print axioms Erdos634.Draft.HalfTurnR4Real.pierced_of
#print axioms Erdos634.Draft.HalfTurnR4Real.Qk_lt
#print axioms Erdos634.Draft.HalfTurnR4Real.Qk_interior

#print axioms Erdos634.Draft.HalfTurnR4Real.vstep
#print axioms Erdos634.Draft.HalfTurnR4Real.qstep
#print axioms Erdos634.Draft.HalfTurnR4Real.band_end
#print axioms Erdos634.Draft.HalfTurnR4Real.t2pprime_forced'
#print axioms Erdos634.Draft.HalfTurnR4Real.t2pprime_real
#print axioms Erdos634.Draft.HalfTurnR4Real.r4_figure_at_pprime'
#print axioms Erdos634.Draft.HalfTurnR4Real.r4_figure_real
#print axioms Erdos634.Draft.HalfTurnR4Real.third_side
#print axioms Erdos634.Draft.HalfTurnR4Real.across_J1_not_b
#print axioms Erdos634.Draft.HalfTurnR4Real.pprime_across_J1_all
#print axioms Erdos634.Draft.HalfTurnR4Real.pprime_order'
#print axioms Erdos634.Draft.HalfTurnR4Real.pprime_order_real
#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.line_interior
#print axioms Erdos634.Draft.HalfTurnR3R4Glue.HFrame.line_mem_bound
