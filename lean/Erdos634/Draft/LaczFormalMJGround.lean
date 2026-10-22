import Erdos634.Draft.LaczFormalMJTile

/-!
# Heights, the ground below a level, and the junction tiles (rule `M(j)`)

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `ht z`: the lattice height of a point (`ht (pt x y) = y`).  `Below ρ i`: all vertices of tile `i` have height `≤ ρ`.
* `Ground ρ k`: the level `ρ = 0` (the base of the target), or `ρ = ρ'+1` and the lattice cells `UpCell x ρ'`,
  `DownCell x ρ'` exist for all `x ≤ k` (the tops of these down tiles are the near side of the fault line `Λ_ρ`).
* `ground_junction`: at the junction `(x, ρ)`, `1 ≤ x ≤ k`, `ρ ≥ 1`, three tiles below `Λ_ρ` present `γ, β, α`; at
  the leg point `(0, ρ)` two tiles below present `γ, α`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar

variable {N : ℕ}

theorem _root_.Erdos634.LaczJunction.TileVerts.pts_mem {T : Tri} {A B C : Plane} (h : TileVerts T A B C)
    (k : Fin 3) : T.pts k = A ∨ T.pts k = B ∨ T.pts k = C := by
  have F3 : ∀ j k : Fin 3, k = j ∨ k = j + 1 ∨ k = j + 2 := by decide
  obtain ⟨j, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ := h
  · rcases F3 j k with rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  · rcases F3 j k with rfl | rfl | rfl
    · exact Or.inl h1
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h3)

theorem _root_.Erdos634.LaczJunction.TileVerts.vertex_A {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    ∃ k, T.pts k = A := by
  obtain ⟨j, ⟨h1, -, -⟩ | ⟨h1, -, -⟩⟩ := h <;> exact ⟨j, h1⟩

theorem _root_.Erdos634.LaczJunction.TileVerts.vertex_C {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    ∃ k, T.pts k = C := h.rot.rot.vertex_A

theorem _root_.Erdos634.LaczJunction.TileVerts.vertex_B {T : Tri} {A B C : Plane} (h : TileVerts T A B C) :
    ∃ k, T.pts k = B := h.rot.vertex_A

namespace LFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : LFrame D e f α β γ p q r)

/-- The lattice height of a point. -/
noncomputable def ht (z : Plane) : ℝ := cross F.e0 (z - D.target.pts p) / cross F.e0 F.v

theorem ht_pt (x y : ℝ) : F.ht (F.pt x y) = y := by
  unfold ht
  have : F.pt x y - D.target.pts p = x • F.e0 + y • F.v := by simp only [pt]; abel
  rw [this, cross_add_right, cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self]
  field_simp [F.hcr.ne']
  ring

/-- All vertices of the tile have height at most `ρ`. -/
def Below (ρ : ℝ) (i : Fin N) : Prop := ∀ k : Fin 3, F.ht ((D.tile i).pts k) ≤ ρ

theorem ht_eq_cross {z : Plane} {ρ : ℝ} : F.ht z = ρ ↔ cross F.e0 (z - D.target.pts p) = ρ * cross F.e0 F.v := by
  unfold ht
  rw [div_eq_iff F.hcr.ne']

theorem ht_sub (z w : Plane) : F.ht z - F.ht w = cross F.e0 (z - w) / cross F.e0 F.v := by
  unfold ht
  rw [← sub_div, ← cross_sub_right]; congr 2; abel

theorem below_of_verts {i : Fin N} {A B C : Plane} {ρ : ℝ} (h : TileVerts (D.tile i) A B C)
    (hA : F.ht A ≤ ρ) (hB : F.ht B ≤ ρ) (hC : F.ht C ≤ ρ) : F.Below ρ i := by
  intro k
  rcases h.pts_mem k with h | h | h <;> rw [h] <;> assumption

/-- Up cells have all vertices of height `≤ y + 1`. -/
theorem up_below {x y : ℝ} (h : F.UpCell x y) : ∃ i, TileVerts (D.tile i) (F.pt x y) (F.pt (x + 1) y)
    (F.pt x (y + 1)) ∧ F.Below (y + 1) i := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, hi, F.below_of_verts hi ?_ ?_ ?_⟩ <;> rw [F.ht_pt] <;> linarith

theorem down_below {x y : ℝ} (h : F.DownCell x y) : ∃ i, TileVerts (D.tile i) (F.pt (x + 1) y)
    (F.pt x (y + 1)) (F.pt (x + 1) (y + 1)) ∧ F.Below (y + 1) i := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, hi, F.below_of_verts hi ?_ ?_ ?_⟩ <;> rw [F.ht_pt] <;> linarith

/-- A tile with a vertex of height `> ρ` is not `Below ρ`. -/
theorem not_below_of_vertex {i : Fin N} {ρ : ℝ} {k : Fin 3} (h : ρ < F.ht ((D.tile i).pts k)) :
    ¬ F.Below ρ i := fun hb => absurd (hb k) (not_le.mpr h)

/-- A tile with a vertex `Z` of height `> ρ` is not `Below ρ`. -/
theorem not_below_of_TV {i : Fin N} {A B Z : Plane} {ρ : ℝ} (hv : TileVerts (D.tile i) A B Z)
    (h : ρ < F.ht Z) : ¬ F.Below ρ i := by
  obtain ⟨k, hk⟩ := hv.vertex_C
  exact F.not_below_of_vertex (k := k) (by rw [hk]; exact h)

/-- The ground below level `ρ` over `x ∈ [0,k]`. -/
def Ground (ρ k : ℕ) : Prop :=
  ρ = 0 ∨ ∃ ρ' : ℕ, ρ = ρ' + 1 ∧ ∀ x : ℕ, x ≤ k → F.UpCell (x : ℝ) (ρ' : ℝ) ∧ F.DownCell (x : ℝ) (ρ' : ℝ)

theorem Ground.mono {ρ k k' : ℕ} (h : F.Ground ρ k) (hk : k' ≤ k) : F.Ground ρ k' := by
  rcases h with h | ⟨ρ', hρ, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨ρ', hρ, fun x hx => h x (hx.trans hk)⟩

/-- Tiles below `Λ_ρ` at the junction `(x, ρ)`, `1 ≤ x ≤ k`, `ρ ≥ 1`: `γ` (up tile), `β`, `α` (down tiles). -/
theorem ground_junction {ρ k x : ℕ} (hG : F.Ground (ρ + 1) k) (hx1 : 1 ≤ x) (hxk : x ≤ k) :
    ∃ iγ iβ iα : Fin N, (D.tile iγ).localAngle (F.pt x (ρ + 1)) = γ ∧
      (D.tile iβ).localAngle (F.pt x (ρ + 1)) = β ∧ (D.tile iα).localAngle (F.pt x (ρ + 1)) = α ∧
      F.Below (ρ + 1 : ℕ) iγ ∧ F.Below (ρ + 1 : ℕ) iβ ∧ F.Below (ρ + 1 : ℕ) iα := by
  rcases hG with h | ⟨ρ', hρ, h⟩
  · omega
  · have hρ' : ρ' = ρ := by omega
    subst hρ'
    obtain ⟨hu, hd⟩ := h x hxk
    obtain ⟨hu0, hd0⟩ := h (x - 1) (by omega)
    obtain ⟨iu, hiu, hbu⟩ := F.up_below hu
    obtain ⟨id1, hid1, hbd1⟩ := F.down_below hd
    obtain ⟨id0, hid0, hbd0⟩ := F.down_below hd0
    have hx : (x : ℝ) = ((x - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hx1]; push_cast; ring
    refine ⟨iu, id0, id1, ?_, ?_, ?_, by simpa using hbu, by simpa using hbd0, by simpa using hbd1⟩
    · have := (F.up_angles hiu).2.2
      simpa using this
    · have := (F.down_angles hid0).2.2
      rw [← hx] at this
      simpa using this
    · have := (F.down_angles hid1).2.1
      simpa using this

/-- Tiles below `Λ_ρ` at the leg point `(0, ρ)`, `ρ ≥ 1`: `γ` (up tile) and `α` (down tile). -/
theorem ground_leg {ρ k : ℕ} (hG : F.Ground (ρ + 1) k) :
    ∃ iγ iα : Fin N, (D.tile iγ).localAngle (F.pt 0 (ρ + 1)) = γ ∧
      (D.tile iα).localAngle (F.pt 0 (ρ + 1)) = α ∧ F.Below (ρ + 1 : ℕ) iγ ∧ F.Below (ρ + 1 : ℕ) iα := by
  rcases hG with h | ⟨ρ', hρ, h⟩
  · omega
  · have hρ' : ρ' = ρ := by omega
    subst hρ'
    obtain ⟨hu, hd⟩ := h 0 (Nat.zero_le _)
    obtain ⟨iu, hiu, hbu⟩ := F.up_below hu
    obtain ⟨id1, hid1, hbd1⟩ := F.down_below hd
    refine ⟨iu, id1, ?_, ?_, by simpa using hbu, by simpa using hbd1⟩
    · have := (F.up_angles hiu).2.2
      simpa using this
    · have := (F.down_angles hid1).2.1
      simpa using this

/-- Standard rows `lv, …, lv+s-1` give the ground at level `lv+s` over `x ≤ k` when `k + s ≤ m`. -/
theorem ground_of_rows {lv m s k : ℕ} (hs1 : 1 ≤ s) (hk : k + s ≤ m)
    (hU : ∀ x : ℕ, x + (s - 1) ≤ m → F.UpCell (x : ℝ) ((lv : ℝ) + ((s - 1 : ℕ) : ℝ)))
    (hDn : ∀ x : ℕ, x + (s - 1) + 1 ≤ m → F.DownCell (x : ℝ) ((lv : ℝ) + ((s - 1 : ℕ) : ℝ))) :
    F.Ground (lv + s) k := by
  right
  refine ⟨lv + (s - 1), by omega, fun x hx => ?_⟩
  have hc : ((lv + (s - 1) : ℕ) : ℝ) = (lv : ℝ) + ((s - 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hc]
  exact ⟨hU x (by omega), hDn x (by omega)⟩

end LFrame

end Erdos634.LaczMJ
