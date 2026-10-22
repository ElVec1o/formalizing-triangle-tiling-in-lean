import Erdos634.Draft.FluxCBoundary
import Erdos634.Draft.FluxCancel
import Erdos634.Draft.FluxCore

/-!
# Beeson (arXiv 1206.2229v4) Lemma 12, generic part: the flux sign is a proper 2-colouring of the tiles

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 12, Lemmas 20-22), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Lemma 12: if a triangle `ABC` is `N`-tiled by a tile with `3 alpha + 2 beta = pi` (and not similar to the
tile), the tiles can be coloured black/white so that tiles on opposite sides of every interior edge have opposite
colours.  Printed proof: parity of edge crossings along paths (planar homotopy).  HERE (route differs, named): the colour
of a tile is the sign of its `Phi_1`-value (Beeson Lemma 21) = the weight of the direction of any of its edges for a
`+-1` direction character `G` all of whose exterior-angle values `G.chi (pi - phi)` are `1` on the tile's angles; two
tiles on opposite sides of a common edge segment have opposite edge directions (`Dissection.leftUnit_neg`, which uses
that the interiors are disjoint) and `G.weight_odd` gives opposite signs.

Adjacency (non edge-to-edge dissections allowed): `Dissection.Adj D i j`: `i != j` and some edge of `i` and some edge of
`j` both contain two distinct common points `p != q` (a common boundary segment of positive length, lying on an edge of
each tile).  Beeson's "tiles touching along a line segment"; for a dissection that is edge-to-edge this is "share an
edge".  Not proved here: that the adjacency graph is connected (so the colouring is unique up to swapping colours).
-/

open scoped Classical

namespace Erdos634.Geometry

open Set

variable {N : ℕ}

/-- **Adjacency of tiles**: a boundary segment of positive length lies in an edge of each tile. -/
def Dissection.Adj (D : Dissection N) (i j : Fin N) : Prop :=
  i ≠ j ∧ ∃ (k l : Fin 3) (p q : Plane), p ≠ q ∧ p ∈ (D.tile i).edge k ∧ q ∈ (D.tile i).edge k ∧
    p ∈ (D.tile j).edge l ∧ q ∈ (D.tile j).edge l

/-- A **proper 2-colouring** (Beeson Lemma 12): colours `+-1`, adjacent tiles get opposite colours. -/
def Dissection.ProperColouring (D : Dissection N) (ε : Fin N → ℤ) : Prop :=
  (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i j, D.Adj i j → ε i = - ε j

theorem Dissection.Adj.symm {D : Dissection N} {i j : Fin N} (h : D.Adj i j) : D.Adj j i := by
  obtain ⟨hne, k, l, p, q, hpq, h1, h2, h3, h4⟩ := h
  exact ⟨hne.symm, l, k, p, q, hpq, h3, h4, h1, h2⟩

/-- **Adjacent tiles have opposite edge directions** (interiors disjoint). -/
theorem Dissection.Adj.leftUnit_neg {D : Dissection N} {i j : Fin N} (h : D.Adj i j) :
    ∃ k l : Fin 3, (D.tile j).leftUnit l = Dir.neg ((D.tile i).leftUnit k) := by
  obtain ⟨hne, k, l, p, q, hpq, h1, h2, h3, h4⟩ := h
  obtain ⟨-, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq h1 h2
  obtain ⟨-, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq h3 h4
  have hm1 : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ (D.tile i).edge k :=
    (mem_ne_ends_of_avg hpq h1 h2).1
  have hm2 : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ (D.tile j).edge l :=
    (mem_ne_ends_of_avg hpq h3 h4).1
  obtain ⟨hz₁, hp₁⟩ := (D.tile i).onEdge_param hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile j).onEdge_param hm2 hn2A hn2B
  have hshift : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have hkey := D.leftUnit_neg hne hz₁ hp₁ hz₂ hp₂
  simp only [hshift] at hkey
  exact ⟨k, l, hkey⟩

/-- On a tile all of whose exterior-angle values are `1`, all three edge weights coincide. -/
theorem Tri.weight_const (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (hext : ∀ k, G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1) (k : Fin 3) :
    G.weight (T.leftUnit k) = G.weight (T.leftUnit 0) := by
  rcases T.det_pos_or_neg with hT | hT
  · have w1 := T.weight_succ_of_pos G hT h 0
    have w2 := T.weight_succ_of_pos G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w1 w2
    rw [hext 1, one_mul] at w1
    rw [hext 2, one_mul] at w2
    fin_cases k
    · rfl
    · exact w1
    · exact w2.trans w1
  · have w0 := T.weight_succ_of_neg G hT h 0
    have w1 := T.weight_succ_of_neg G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w0 w1
    rw [hext 1, one_mul] at w0
    rw [hext 2, one_mul] at w1
    fin_cases k
    · rfl
    · exact w0.symm
    · exact w1.symm.trans w0.symm

/-- **THE FLUX COLOURING IS PROPER** (generic form of Beeson Lemma 12).  Let `G` be a `+-1` grid character, `D` a
dissection into copies of one tile whose angles lie in `G.L` and have exterior-angle value `1`.  Then there are signs
`eps i = +-1` with: tile `i` has flux `eps i * K` (`K` the model's tile value), adjacent tiles have opposite signs, and
the target flux is `(sum eps) * K`. -/
theorem CongruentDissection.flux_colouring (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (hext : ∀ k, G.chi ((Real.pi - D.model.angleAt k : ℝ) : Real.Angle) = 1) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧
      (∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * G.tileValue D.model) ∧
      D.target.flux G.weight = ((∑ i, ε i : ℤ) : ℝ) * G.tileValue D.model := by
  -- tile data
  have hang : ∀ i k, ∃ m, (D.tile i).angleAt k = D.model.angleAt m := by
    intro i k
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    exact ⟨σ k, (hσ k).1⟩
  have hi : ∀ i k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro i k
    obtain ⟨m, hm⟩ := hang i k
    rw [hm]; exact hmodel m
  have hie : ∀ i k, G.chi ((Real.pi - (D.tile i).angleAt k : ℝ) : Real.Angle) = 1 := by
    intro i k
    obtain ⟨m, hm⟩ := hang i k
    rw [hm]; exact hext m
  have hw : ∀ i, G.weight ((D.tile i).leftUnit 0) = 1 ∨ G.weight ((D.tile i).leftUnit 0) = -1 := by
    intro i
    have := G.val_sq hsq ((D.tile i).leftUnit 0).angle
    exact mul_self_eq_one_iff.mp this
  let ε : Fin N → ℤ := fun i => if G.weight ((D.tile i).leftUnit 0) = 1 then 1 else -1
  have hε : ∀ i, ((ε i : ℤ) : ℝ) = G.weight ((D.tile i).leftUnit 0) := by
    intro i
    by_cases h1 : G.weight ((D.tile i).leftUnit 0) = 1
    · show (((if G.weight ((D.tile i).leftUnit 0) = 1 then 1 else -1 : ℤ)) : ℝ) = _
      rw [if_pos h1, h1]; norm_num
    · rcases hw i with h2 | h2
      · exact absurd h2 h1
      · show (((if G.weight ((D.tile i).leftUnit 0) = 1 then 1 else -1 : ℤ)) : ℝ) = _
        rw [if_neg h1, h2]; norm_num
  have hε1 : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases h1 : G.weight ((D.tile i).leftUnit 0) = 1
    · left; exact if_pos h1
    · right; exact if_neg h1
  have hflux : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * G.tileValue D.model := by
    intro i
    rw [(D.tile i).flux_eq_edgeSign G hsq (hi i) 0, G.tileValue_congr (D.tiles_congruent i), hε]
    unfold GridChar.edgeSign
    rw [hie i (0 + 2), one_mul]
  refine ⟨ε, ⟨hε1, ?_⟩, hflux, ?_⟩
  · intro i j hadj
    obtain ⟨k, l, hkl⟩ := hadj.leftUnit_neg
    have hjl : G.weight ((D.tile j).leftUnit l) = G.weight ((D.tile j).leftUnit 0) :=
      (D.tile j).weight_const G (hi j) (hie j) l
    have hik : G.weight ((D.tile i).leftUnit k) = G.weight ((D.tile i).leftUnit 0) :=
      (D.tile i).weight_const G (hi i) (hie i) k
    have h : G.weight ((D.tile j).leftUnit 0) = - G.weight ((D.tile i).leftUnit 0) := by
      rw [← hjl, ← hik, hkl, G.weight_odd]
    have hr : ((ε j : ℤ) : ℝ) = - ((ε i : ℤ) : ℝ) := by rw [hε, hε, h]
    have : ε j = - ε i := by exact_mod_cast hr
    omega
  · rw [← D.flux_cancel G.weight G.weight_odd, Finset.sum_congr rfl fun i _ => hflux i,
      ← Finset.sum_mul]
    push_cast
    rfl

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.Adj.leftUnit_neg
#print axioms Erdos634.Geometry.CongruentDissection.flux_colouring
