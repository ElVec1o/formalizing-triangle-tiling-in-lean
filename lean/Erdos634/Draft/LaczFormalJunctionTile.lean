import Erdos634.CornerBaseEdgesReal
import Erdos634.CongruentTileEdges
import Erdos634.TileAt

/-!
# Band junction rules: tile-level facts for a real `CongruentDissection`

Erdős #634, base-`β` band.  Credit: AI assistant (band lemma / item-3 proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.

For a tile of a `CongruentDissection` whose model has pairwise distinct sides
`a = sideOpp 0`, `b = sideOpp 1`, `c = sideOpp 2` (opposite `α, β, γ`):

* `tile_vertex_cases` — at each vertex, either the corner angle is `α` or `γ`, or it is `β` and the
  side opposite is `b`;
* `bedge_end_angle` — an end of an edge of length `b` carries `α` or `γ`, never `β`;
* `edge_length_mem` — every tile edge has length `a`, `b` or `c`;
* `unique_bedge` — a tile has at most one edge of length `b`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczJunction

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.CornerBaseEdgesReal

variable {N : ℕ}

/-- The side multiset of a tile of a congruent dissection, listed from vertex `j`. -/
theorem tile_multiset (D : CongruentDissection N) (i : Fin N) (j : Fin 3) :
    ({dist ((D.tile i).pts j) ((D.tile i).pts (j+1)),
      dist ((D.tile i).pts (j+2)) ((D.tile i).pts j),
      dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2))} : Multiset ℝ)
      = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} := by
  have hmulti := (D.tiles_congruent i).sideMultiset_eq
  have hshift := Tri.sideMultiset_shift (D.tile i) j
  rw [hshift, hmulti]
  simp only [sideOpp, show (2:Fin 3)+1=0 from rfl, show (2:Fin 3)+2=1 from rfl,
    show (0:Fin 3)+1=1 from rfl, show (0:Fin 3)+2=2 from rfl,
    show (1:Fin 3)+1=2 from rfl, show (1:Fin 3)+2=0 from rfl]

/-- Two sides equal to `b` are impossible when `a,b,c` are pairwise distinct. -/
theorem no_two_b (D : CongruentDissection N)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (i : Fin N) (j : Fin 3) (x y z : ℝ)
    (hm : ({x, y, z} : Multiset ℝ) = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0})
    (h1 : x = sideOpp D.model 1) (h2 : y = sideOpp D.model 1) : False := by
  have := congrArg (Multiset.count (sideOpp D.model 1)) hm
  rw [h1, h2] at this
  simp [Multiset.count_cons, hab.symm, hbc] at this

theorem no_two_b' (D : CongruentDissection N)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (x y z : ℝ)
    (hm : ({x, y, z} : Multiset ℝ) = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0})
    (h1 : x = sideOpp D.model 1) (h3 : z = sideOpp D.model 1) : False := by
  have := congrArg (Multiset.count (sideOpp D.model 1)) hm
  rw [h1, h3] at this
  simp [Multiset.count_cons, hab.symm, hbc] at this

theorem no_two_b'' (D : CongruentDissection N)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (x y z : ℝ)
    (hm : ({x, y, z} : Multiset ℝ) = {sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0})
    (h2 : y = sideOpp D.model 1) (h3 : z = sideOpp D.model 1) : False := by
  have := congrArg (Multiset.count (sideOpp D.model 1)) hm
  rw [h2, h3] at this
  simp [Multiset.count_cons, hab.symm, hbc] at this <;> split_ifs at this <;> omega

/-- **Vertex cases.**  At vertex `j` of a tile, the corner angle is `α` or `γ`, or it is `β`
and the opposite side has length `b`. -/
theorem tile_vertex_cases (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (i : Fin N) (j : Fin 3) :
    (D.tile i).localAngle ((D.tile i).pts j) = α ∨ (D.tile i).localAngle ((D.tile i).pts j) = γ ∨
      dist ((D.tile i).pts (j+1)) ((D.tile i).pts (j+2)) = sideOpp D.model 1 := by
  obtain ⟨k0, hk0angle, hk0side⟩ := congruent_opposite_side (D.tiles_congruent i).symm j
  rw [Tri.localAngle_vertex, hk0angle]
  fin_cases k0
  · left; exact hα'
  · right; right; rw [← hk0side]; simp [sideOpp]
  · right; left; exact hγ'


/-- An end of an edge of length `b` carries `α` or `γ`, never `β` (first end). -/
theorem bedge_end_angle (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (i : Fin N) (j : Fin 3)
    (h : dist ((D.tile i).pts j) ((D.tile i).pts (j+1)) = sideOpp D.model 1) :
    (D.tile i).localAngle ((D.tile i).pts j) = α ∨ (D.tile i).localAngle ((D.tile i).pts j) = γ := by
  rcases tile_vertex_cases D α β γ hα' hβ' hγ' i j with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact (no_two_b' D hab hbc _ _ _ (tile_multiset D i j) h h1).elim

/-- ... and for the other incident edge. -/
theorem bedge_end_angle' (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (i : Fin N) (j : Fin 3)
    (h : dist ((D.tile i).pts (j+2)) ((D.tile i).pts j) = sideOpp D.model 1) :
    (D.tile i).localAngle ((D.tile i).pts j) = α ∨ (D.tile i).localAngle ((D.tile i).pts j) = γ := by
  rcases tile_vertex_cases D α β γ hα' hβ' hγ' i j with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact (no_two_b'' D hab hbc _ _ _ (tile_multiset D i j) h h1).elim

/-- **Both ends of a `b`-edge carry `α` or `γ`**, in terms of the edge `(k, k+1)`. -/
theorem bedge_both_ends (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (i : Fin N) (k : Fin 3)
    (h : dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 1) :
    ((D.tile i).localAngle ((D.tile i).pts k) = α ∨ (D.tile i).localAngle ((D.tile i).pts k) = γ) ∧
    ((D.tile i).localAngle ((D.tile i).pts (k+1)) = α ∨
      (D.tile i).localAngle ((D.tile i).pts (k+1)) = γ) := by
  refine ⟨bedge_end_angle D α β γ hα' hβ' hγ' hab hbc i k h, ?_⟩
  apply bedge_end_angle' D α β γ hα' hβ' hγ' hab hbc i (k+1)
  have : k + 1 + 2 = k := by fin_cases k <;> rfl
  rw [this]; exact h

/-- A tile has at most one edge of length `b`. -/
theorem two_bedges (D : CongruentDissection N)
    (hab : sideOpp D.model 0 ≠ sideOpp D.model 1) (hbc : sideOpp D.model 1 ≠ sideOpp D.model 2)
    (i : Fin N) (k k' : Fin 3)
    (h : dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 1)
    (h' : dist ((D.tile i).pts k') ((D.tile i).pts (k'+1)) = sideOpp D.model 1) : k = k' := by
  by_contra hne
  rcases fin3_cases k' k (Ne.symm hne) with e | e
  · subst e
    have h3 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
    rw [h3] at h'
    exact no_two_b' D hab hbc _ _ _ (tile_multiset D i k) h h'
  · subst e
    have h3 : k + 2 + 1 = k := by fin_cases k <;> rfl
    rw [h3] at h'
    exact no_two_b D hab hbc i k _ _ _ (tile_multiset D i k) h h' |>.elim

/-- Every tile edge has length `a`, `b` or `c`. -/
theorem edge_length_mem (D : CongruentDissection N) (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 2 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 1 ∨
    dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) = sideOpp D.model 0 := by
  have hm := tile_multiset D i k
  have : dist ((D.tile i).pts k) ((D.tile i).pts (k+1)) ∈
      ({sideOpp D.model 2, sideOpp D.model 1, sideOpp D.model 0} : Multiset ℝ) := by
    rw [← hm]; simp
  simpa using this

end Erdos634.LaczJunction
