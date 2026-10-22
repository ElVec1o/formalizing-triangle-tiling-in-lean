/-
Draft/H1eCLFacts.lean — atom H1.e (CL), part 3: the corner facts D7 needs, stated for the REAL tiles of a
`RightNormal` dissection, in terms of `D.tile`, `localAngle`, edge lengths and the collinearity predicate `Col`
(the same predicate `H1iSLMain.side_sign_lemma` uses to characterise the tile edges lying on a side).

Notation (normal form): model `a = oppLen 0` (opposite α), `b = oppLen 1`, `c = oppLen 2` (hypotenuse);
target `B = pts 0`, `C = pts 1`, `A = pts 2`; side `0 = BC`, side `1 = CA`, side `2 = AB`
(side `s` runs from `pts s` to `pts (s+1)`).  `OnSide D s i e` : the tile edge `(i,e)` (from `pts e` to `pts (e+1)`) has both
endpoints collinear with side `s`.

* `cornerB_fact` (paper (B)):  there is a tile with two edges at `B`, one on `AB` and one on `BC`, whose lengths are
  `b` on `AB` & `c` on `BC`, or `c` on `AB` & `b` on `BC`.
* `cornerA_fact` (paper (A)):  some tile edge on `AB` (starting at the apex `A`) has length `a` or `c`.
  (Proof: leg tile at `A` [`ApexPlacement.leg_tile`] with the counts `(0,2,0,0)`: every tile at `A` presents `β`, so its
  edges at `A` are `{a, c}`.)
No irrationality hypothesis beyond `RightNormal.irr` is used.
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry. ***
-/
import Erdos634.Draft.H1eCLAlign
import Erdos634.Draft.H1eCLCount
import Erdos634.Draft.H1iSLChar
import Erdos634.Draft.ApexPlacement
import Erdos634.CongruentTileEdges
import Erdos634.CornerBaseEdgesReal

open scoped Classical

namespace Erdos634.Draft.H1eCL

open Erdos634.Geometry Erdos634.Draft.H1a Erdos634.TilePlacement Erdos634.Geometry.Row3.RP
open Erdos634.H1iSL (Col)
open Erdos634.Draft.CornerAdjacency Erdos634.Draft.ApexPlacement

variable {N : ℕ}

/-- Edge `(i,e)` of the tile lies on side `s` of the target (both endpoints collinear with the side). -/
def OnSide (D : CongruentDissection N) (s : Fin 3) (i : Fin N) (e : Fin 3) : Prop :=
  Col (D.target.pts s) (D.target.pts (s + 1)) ((D.tile i).pts e) ∧
    Col (D.target.pts s) (D.target.pts (s + 1)) ((D.tile i).pts (e + 1))

/-- Length of tile edge `(i,e)`. -/
noncomputable def elen (D : CongruentDissection N) (i : Fin N) (e : Fin 3) : ℝ :=
  dist ((D.tile i).pts e) ((D.tile i).pts (e + 1))

/-! ### Collinearity helpers -/

theorem col_self (P Q : Plane) : Col P Q P := by
  unfold Col; ring

theorem col_swap {P Q X : Plane} (h : Col P Q X) : Col Q P X := by
  unfold Col at h ⊢
  linear_combination (-1 : ℝ) * h

theorem col_right (P Q : Plane) : Col P Q Q := by
  unfold Col; ring

theorem col_of_sameRay {P Q X : Plane} (h : SameRay ℝ (Q - P) (X - P)) : Col P Q X := by
  unfold Col
  rcases h with h0 | h0 | ⟨r1, r2, hr1, hr2, hr⟩
  · have a0 := congrArg (fun v : Plane => v 0) h0
    have a1 := congrArg (fun v : Plane => v 1) h0
    simp only [PiLp.sub_apply, PiLp.zero_apply] at a0 a1
    rw [a0, a1]; ring
  · have a0 := congrArg (fun v : Plane => v 0) h0
    have a1 := congrArg (fun v : Plane => v 1) h0
    simp only [PiLp.sub_apply, PiLp.zero_apply] at a0 a1
    rw [a0, a1]; ring
  · have a0 := congrArg (fun v : Plane => v 0) hr
    have a1 := congrArg (fun v : Plane => v 1) hr
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at a0 a1
    have : r1 * ((Q 0 - P 0) * (X 1 - P 1) - (Q 1 - P 1) * (X 0 - P 0)) = 0 := by
      linear_combination (X 1 - P 1) * a0 - (X 0 - P 0) * a1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hr1.ne'
    · exact h

/-! ### Edge lengths at a vertex of known angle -/

theorem tile_opp_of_angle (D : CongruentDissection N) (i : Fin N) (j k0 : Fin 3) {θ : ℝ}
    (hang : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ)
    (hk0 : D.model.angleAt k0 = θ) (huniq : ∀ k, D.model.angleAt k = θ → k = k0) :
    dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = D.model.oppLen k0 := by
  obtain ⟨k, hk, hs⟩ := Erdos634.CornerBaseEdgesReal.congruent_opposite_side
    (D.tiles_congruent i).symm j
  have hkθ : D.model.angleAt k = θ := by rw [← hang]; exact hk.symm
  have := huniq k hkθ
  subst this
  exact hs.symm

theorem tile_multiset (D : CongruentDissection N) (i : Fin N) (j : Fin 3) :
    ({dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)), dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j),
      dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2))} : Multiset ℝ)
      = {D.model.oppLen 2, D.model.oppLen 1, D.model.oppLen 0} := by
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  rw [hshift, hmulti]
  simp only [Tri.oppLen, show (2:Fin 3)+1=0 from rfl, show (2:Fin 3)+2=1 from rfl,
    show (0:Fin 3)+1=1 from rfl, show (0:Fin 3)+2=2 from rfl,
    show (1:Fin 3)+1=2 from rfl, show (1:Fin 3)+2=0 from rfl]

/-- Edges at an `α`-corner of a tile are `{b, c}` (as an unordered pair). -/
theorem edges_alpha {α : ℝ} (h : RightNormal D α) (i : Fin N) (j : Fin 3)
    (hang : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = α) :
    (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = D.model.oppLen 1 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = D.model.oppLen 2) ∨
    (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = D.model.oppLen 2 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = D.model.oppLen 1) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := h.ne_facts
  have hb := h.hβ
  have hopp := tile_opp_of_angle D i j 0 hang h.m0 (by
    intro k hk
    fin_cases k
    · rfl
    · exact absurd (hb.symm.trans hk) (Ne.symm n1)
    · exact absurd (h.m2.symm.trans hk) (Ne.symm n2))
  exact corner_tile_edges (D.tile i) j (D.model.oppLen 1) (D.model.oppLen 0) (D.model.oppLen 2)
    (oppLen_pos _ _).ne' hopp (by
      rw [tile_multiset D i j]
      show ({_, _, _} : Multiset ℝ) = {_, _, _}
      simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      simp only [add_comm, add_assoc, add_left_comm])

/-- Edges at a `β`-corner of a tile are `{a, c}` (as an unordered pair). -/
theorem edges_beta {α : ℝ} (h : RightNormal D α) (i : Fin N) (j : Fin 3)
    (hang : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
      = Real.pi / 2 - α) :
    (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = D.model.oppLen 0 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = D.model.oppLen 2) ∨
    (dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = D.model.oppLen 2 ∧
      dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) = D.model.oppLen 0) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := h.ne_facts
  have hb := h.hβ
  have hopp := tile_opp_of_angle D i j 1 hang hb (by
    intro k hk
    fin_cases k
    · exact absurd (h.m0.symm.trans hk) n1
    · rfl
    · exact absurd (h.m2.symm.trans hk) (Ne.symm n5))
  exact corner_tile_edges (D.tile i) j (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2)
    (oppLen_pos _ _).ne' hopp (by
      rw [tile_multiset D i j]
      show ({_, _, _} : Multiset ℝ) = {_, _, _}
      simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add]
      simp only [add_comm, add_assoc])

/-! ### Corner B -/

private theorem fin_a : ∀ j : Fin 3, j + 2 + 1 = j := by decide

/-- **Corner `B`.**  A single tile has two edges at `B`, one on `AB` (side 2) and one on `BC` (side 0); their lengths are
`(b on AB, c on BC)` or `(c on AB, b on BC)`. -/
theorem cornerB_fact {α : ℝ} (h : RightNormal D α) :
    ∃ (i : Fin N) (e e' : Fin 3),
      (OnSide D 2 i e ∧ elen D i e = D.model.oppLen 1 ∧ OnSide D 0 i e' ∧ elen D i e' = D.model.oppLen 2) ∨
      (OnSide D 2 i e ∧ elen D i e = D.model.oppLen 2 ∧ OnSide D 0 i e' ∧ elen D i e' = D.model.oppLen 1) := by
  obtain ⟨i, hi⟩ := h.cornerB_tile
  have hc : cornerAngle (D.target.pts (0 + 1)) (D.target.pts 0) (D.target.pts (0 + 2)) = α := h.t0
  obtain ⟨j, hj, hal⟩ := corner_aligned D.toDissection 0 i hc hi
  have hang : cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = α := by
    rw [← Tri.localAngle_vertex, ← hj]; exact hi
  have hedges := edges_alpha h i j hang
  -- the two edges at the vertex: `j` (to `j+1`) and `j+2` (from `j+2` back to `j`)
  have e2 : elen D i (j + 2) = dist ((D.tile i).pts (j + 2)) ((D.tile i).pts j) := by
    unfold elen; rw [fin_a j]
  have e1 : elen D i j = dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) := rfl
  have hBpt : (D.tile i).pts j = D.target.pts 0 := hj.symm
  have hp0 : (0 : Fin 3) + 1 = 1 := rfl
  have hp02 : (0 : Fin 3) + 2 = 2 := rfl
  have hp21 : (2 : Fin 3) + 1 = 0 := rfl
  -- `OnSide` for an edge starting at `B` along the ray towards `target.pts 1` (side 0)
  have s0_first : ∀ X : Plane, SameRay ℝ (D.target.pts (0 + 1) - D.target.pts 0) (X - D.target.pts 0) →
      Col (D.target.pts 0) (D.target.pts (0 + 1)) X := fun X hr => col_of_sameRay hr
  -- ray towards `target.pts 2` (= A): side 2 is `Col (pts 2) (pts (2+1)=pts 0)`
  have s2_first : ∀ X : Plane, SameRay ℝ (D.target.pts (0 + 2) - D.target.pts 0) (X - D.target.pts 0) →
      Col (D.target.pts 2) (D.target.pts (2 + 1)) X := by
    intro X hr
    rw [hp21]
    rw [hp02] at hr
    exact col_swap (col_of_sameRay hr)
  have colB0 : Col (D.target.pts 0) (D.target.pts (0 + 1)) (D.target.pts 0) := col_self _ _
  have colB2 : Col (D.target.pts 2) (D.target.pts (2 + 1)) (D.target.pts 0) := by
    rw [hp21]; exact col_right _ _
  rcases hal with ⟨r1, r2⟩ | ⟨r1, r2⟩
  · -- edge `j` along BC (side 0), edge `j+2` along BA (side 2)
    have o0 : OnSide D 0 i j := ⟨by rw [hBpt]; exact colB0, s0_first _ r1⟩
    have o2 : OnSide D 2 i (j + 2) := ⟨s2_first _ r2, by rw [fin_a j, hBpt]; exact colB2⟩
    refine ⟨i, j + 2, j, ?_⟩
    rcases hedges with ⟨l1, l2⟩ | ⟨l1, l2⟩
    · right; exact ⟨o2, by rw [e2]; exact l2, o0, by rw [e1]; exact l1⟩
    · left; exact ⟨o2, by rw [e2]; exact l2, o0, by rw [e1]; exact l1⟩
  · -- edge `j` along BA (side 2), edge `j+2` along BC (side 0)
    have o2 : OnSide D 2 i j := ⟨by rw [hBpt]; exact colB2, s2_first _ r1⟩
    have o0 : OnSide D 0 i (j + 2) := ⟨s0_first _ r2, by rw [fin_a j, hBpt]; exact colB0⟩
    refine ⟨i, j, j + 2, ?_⟩
    rcases hedges with ⟨l1, l2⟩ | ⟨l1, l2⟩
    · left; exact ⟨o2, by rw [e1]; exact l1, o0, by rw [e2]; exact l2⟩
    · right; exact ⟨o2, by rw [e1]; exact l1, o0, by rw [e2]; exact l2⟩

/-! ### Corner A -/

/-- **Corner `A` (apex).**  Some tile edge on `AB` (side 2) has length `a` or `c`. -/
theorem cornerA_fact {α : ℝ} (h : RightNormal D α) :
    ∃ (i : Fin N) (e : Fin 3), OnSide D 2 i e ∧
      (elen D i e = D.model.oppLen 0 ∨ elen D i e = D.model.oppLen 2) := by
  have hπ := Real.pi_pos
  have h0 := h.pos
  have h2 := h.lt
  have hβ0 : Real.pi / 2 - α ≠ 0 := by intro e; linarith
  have hβπ : Real.pi / 2 - α ≠ Real.pi := by intro e; linarith
  have hβ2π : Real.pi / 2 - α ≠ 2 * Real.pi := by intro e; linarith
  -- every tile containing `A` has `A` as a vertex, with local angle β
  have hvert : ∀ i, D.target.pts 2 ∈ (D.tile i).carrier → ∃ j, (D.tile i).pts j = D.target.pts 2 := by
    intro i hi
    have hne := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile i) hi
    rcases h.cornerA_vals i with e | e
    · obtain ⟨j, hj⟩ := Erdos634.ApexEdgesReal.isVertex_of_localAngle_ne (D.tile i) hβ2π hβπ hβ0 e
      exact ⟨j, hj.symm⟩
    · exact absurd e hne
  have hC := apexCone_target D.target 2
  obtain ⟨i, m, hm, U', W', hUW, S, hS, hU, -⟩ := leg_tile D.toDissection hC hvert
  -- the tile's local angle at `A` is β
  have hAmem : D.target.pts 2 ∈ (D.tile i).carrier := by
    rw [← hm]; exact subset_convexHull ℝ _ (Set.mem_range_self m)
  have hne := Erdos634.MarchFlank.localAngle_ne_zero_of_mem (D.tile i) hAmem
  have hloc : (D.tile i).localAngle (D.target.pts 2) = Real.pi / 2 - α := by
    rcases h.cornerA_vals i with e | e
    · exact e
    · exact absurd e hne
  have hang : cornerAngle ((D.tile i).pts (m + 1)) ((D.tile i).pts m) ((D.tile i).pts (m + 2))
      = Real.pi / 2 - α := by
    rw [← Tri.localAngle_vertex, hm]; exact hloc
  have hedges := edges_beta h i m hang
  have hp21 : (2 : Fin 3) + 1 = 0 := rfl
  have e1 : elen D i m = dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) := rfl
  have e2 : elen D i (m + 2) = dist ((D.tile i).pts (m + 2)) ((D.tile i).pts m) := by
    unfold elen; rw [fin_a m]
  have hQ : D.target.pts (2 + 1) - D.target.pts 2 = S • U' := hU
  have hray : ∀ X : Plane, U' = X - D.target.pts 2 →
      SameRay ℝ (D.target.pts (2 + 1) - D.target.pts 2) (X - D.target.pts 2) := by
    intro X hX
    rw [hQ, hX]
    exact SameRay.sameRay_pos_smul_left _ hS
  have colA : Col (D.target.pts 2) (D.target.pts (2 + 1)) (D.target.pts 2) := col_self _ _
  rcases hUW with ⟨hU1, -⟩ | ⟨hU1, -⟩
  · -- flank along AB is `pts (m+1) - A`: edge `m`
    have hx : U' = (D.tile i).pts (m + 1) - D.target.pts 2 := hU1
    have o2 : OnSide D 2 i m := ⟨by rw [hm]; exact colA, col_of_sameRay (hray _ hx)⟩
    refine ⟨i, m, o2, ?_⟩
    rw [e1]
    rcases hedges with ⟨l1, -⟩ | ⟨l1, -⟩
    · exact Or.inl l1
    · exact Or.inr l1
  · have hx : U' = (D.tile i).pts (m + 2) - D.target.pts 2 := hU1
    have o2 : OnSide D 2 i (m + 2) :=
      ⟨col_of_sameRay (hray _ hx), by rw [fin_a m, hm]; exact colA⟩
    refine ⟨i, m + 2, o2, ?_⟩
    rw [e2]
    rcases hedges with ⟨-, l2⟩ | ⟨-, l2⟩
    · exact Or.inr l2
    · exact Or.inl l2

end Erdos634.Draft.H1eCL

#print axioms Erdos634.Draft.H1eCL.cornerB_fact
#print axioms Erdos634.Draft.H1eCL.cornerA_fact
