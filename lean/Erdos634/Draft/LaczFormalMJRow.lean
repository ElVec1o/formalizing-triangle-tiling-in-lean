import Erdos634.Draft.LaczFormalMJGround

/-!
# The rows of the standard triangle and the horizontal / hypotenuse covers (rule `M(j)`)

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich (chord covers), Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

Notation (all lattice reals): the corner triangle has `m+1` up tiles on level `r`; `D_s = (m+1−s, r+s)` is the point
of the hypotenuse `l` at distance `s·b` from `J = D_0 = (m+1, r)`; `l` ends at the leg point `D_{m+1} = (0, r+m+1)`.
* `Std r m s`: rows `r, …, r+s` of the triangle are standard (`UpCell x (r+t)` for `x+t ≤ m`, `DownCell x (r+t)` for
  `x+t+1 ≤ m`).
* `StrH ρ y`, `StrL x y z`: `y` (resp. `z`) is straddled by an edge of the far chain of the horizontal line `Λ_ρ`
  (the side above) / of the line through `(x,y)` with direction `v − e0` (the side to the right).
* `h_cover`: the far (upper) side of the horizontal chord `[D_s, (0, r+s)]` is covered by `m+1−s` `c`-edges
  at the lattice positions.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

namespace LFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : LFrame D e f α β γ p q r)

/-- `Λ_ρ` is straddled at `y`: an edge of a tile above `Λ_ρ`, on `Λ_ρ`, has `y` in its relative interior. -/
def StrH (ρ : ℝ) (y : Plane) : Prop :=
  Straddled D.toDissection (crossL (-F.e0)) (cross (-F.e0) (F.pt 0 ρ)) y

/-- The line through `(x,y)` with direction `v − e0` is straddled at `z` on the side to its right. -/
def StrL (x y : ℝ) (z : Plane) : Prop :=
  Straddled D.toDissection (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt x y)) z

/-- Rows `r, …, r+s` of the triangle with `m+1` up tiles on level `r` are standard. -/
def Std (r m s : ℕ) : Prop :=
  ∀ t : ℕ, t ≤ s →
    (∀ x : ℕ, x + t ≤ m → F.UpCell (x : ℝ) ((r : ℝ) + t)) ∧
    (∀ x : ℕ, x + t + 1 ≤ m → F.DownCell (x : ℝ) ((r : ℝ) + t))

/-- The bounds that make all lattice points used below lie in the target. -/
def Bnd (H : ℕ) : Prop := (H : ℝ) < F.lam ∧ (H : ℝ) < F.mu

theorem latOK {H : ℕ} (hB : F.Bnd H) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ H) :
    F.LatOK x y := by
  refine ⟨hx, hy, ?_⟩
  have hl := F.hlam
  have hm := F.hmu
  set μ0 := min F.lam F.mu with hμ0
  have hm' : 0 < μ0 := lt_min hl hm
  have hH : (H : ℝ) < μ0 := lt_min hB.1 hB.2
  have h1 : x / F.lam ≤ x / μ0 := div_le_div_of_nonneg_left hx hm' (min_le_left _ _)
  have h2 : y / F.mu ≤ y / μ0 := div_le_div_of_nonneg_left hy hm' (min_le_right _ _)
  have h3 : (x + y) / μ0 ≤ H / μ0 := div_le_div_of_nonneg_right hxy hm'.le
  have h4 : (H : ℝ) / μ0 < 1 := (div_lt_one hm').mpr hH
  have : x / μ0 + y / μ0 = (x + y) / μ0 := by ring
  linarith


theorem e0_ne : F.e0 ≠ 0 := by
  intro h; have := F.hcr; rw [h] at this; simp [cross] at this

theorem v_ne : F.v ≠ 0 := by
  intro h; have := F.hcr; rw [h] at this; simp [cross] at this

theorem tc_pos (S : BandSetup D e f α β γ p q r) : (0 : ℝ) < tc e f := by
  have := b_lt_c e f S.he S.hef
  have := b_pos e f S.he S.hef
  exact_mod_cast (by omega : 0 < tc e f)

/-- **The horizontal cover.** `Λ_ρ`, `ρ = r+s` (`1 ≤ s ≤ m`), is a wall from `D_s = (m+1−s, ρ)` to the leg point
`(0, ρ)` whose near (lower) side is the tops of the down tiles of row `ρ−1`; if no upper edge passes through `D_s`,
the upper side is covered by `m+1−s` `c`-edges at the lattice positions. -/
theorem h_cover {H m r s : ℕ} (hB : F.Bnd H) (hrH : r + m + 1 ≤ H) (hme : m + 1 ≤ e)
    (hs1 : 1 ≤ s) (hsm : s ≤ m) (hStd : F.Std r m (s - 1))
    (hns : ¬ F.StrH ((r : ℝ) + s) (F.pt ((m : ℝ) + 1 - s) ((r : ℝ) + s))) :
    ∀ k : ℕ, k < m + 1 - s →
      ∃ e' ∈ D.lineChain (crossL (-F.e0)) (cross (-F.e0) (F.pt 0 ((r : ℝ) + s))),
        (((D.tile e'.1).pts e'.2 = F.pt ((m : ℝ) + 1 - s - k) ((r : ℝ) + s) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.pt ((m : ℝ) + 1 - s - k - 1) ((r : ℝ) + s)) ∨
         ((D.tile e'.1).pts e'.2 = F.pt ((m : ℝ) + 1 - s - k - 1) ((r : ℝ) + s) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.pt ((m : ℝ) + 1 - s - k) ((r : ℝ) + s))) := by
  classical
  obtain ⟨n', hn'⟩ : ∃ n', n' = m + 1 - s := ⟨_, rfl⟩
  have hn'r : (n' : ℝ) = (m : ℝ) + 1 - s := by
    rw [hn', Nat.cast_sub (by omega)]; push_cast; ring
  have hn'pos : 0 < n' := by omega
  have hn'e : n' < e := by omega
  set ρ : ℝ := (r : ℝ) + s with hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hnr : (0 : ℝ) < n' := by exact_mod_cast hn'pos
  have hPG : F.LatOK (n' : ℝ) ρ := by
    apply F.latOK hB (Nat.cast_nonneg _) (by linarith)
    rw [hn'r, hρ]
    have : (r + m + 1 : ℕ) ≤ H := hrH
    have h2 : ((r + m + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast this
    push_cast at h2
    linarith
  have hG : F.LatOK 0 ρ := by
    apply F.latOK hB le_rfl (by linarith)
    rw [hρ]
    have h2 : ((r + m + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast hrH
    have : (s : ℝ) ≤ m := by exact_mod_cast hsm
    push_cast at h2
    linarith
  set P := F.pt (n' : ℝ) ρ with hP
  set G := F.pt 0 ρ with hG'
  have hPGd : dist P G = (n' : ℝ) * tc e f := by
    rw [hP, hG', F.dist_pt, show ((n' : ℝ) - 0) • F.e0 + (ρ - ρ) • F.v = (n' : ℝ) • F.e0 by module,
      norm_smul, F.he0, Real.norm_of_nonneg hnr.le]
  have hne : P ≠ G := by
    intro h
    rw [h, dist_self] at hPGd
    have := mul_pos hnr (LFrame.tc_pos F.S)
    linarith
  have hg0 : (crossL (-F.e0) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply F.e0_ne
    have : -F.e0 = 0 := by
      apply eq_zero_of_cross_eq_zero
      intro w
      have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h
      simpa using this
    simpa using this
  have hgP : (crossL (-F.e0) : Plane →ₗ[ℝ] ℝ) P = cross (-F.e0) (F.pt 0 ρ) := by
    simp only [crossL_apply, hP, pt]
    simp only [cross, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hgG : (crossL (-F.e0) : Plane →ₗ[ℝ] ℝ) G = cross (-F.e0) (F.pt 0 ρ) := rfl
  -- near side: the tops of the down tiles of row `ρ - 1`
  have hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
      AffineMap.lineMap P G t ∈ (D.tile i).edge k := by
    intro t ht0 ht1
    have hq : ∀ τ : ℝ, F.pt τ ρ = F.pt 0 ρ + τ • F.e0 := by intro τ; simp only [pt]; module
    obtain ⟨i, k, hik⟩ := chain_cover D.toDissection (fun τ => F.pt τ ρ) (F.pt 0 ρ) F.e0 hq n' hn'pos
      (by
        intro t' ht'
        obtain ⟨hu, hd⟩ := (hStd (s - 1) le_rfl)
        have := hd t' (by omega)
        obtain ⟨id, hid⟩ := this
        have hy : ((r : ℝ) + ((s - 1 : ℕ) : ℝ)) + 1 = ρ := by
          rw [hρ, Nat.cast_sub hs1]; push_cast; ring
        have hid' : TileVerts (D.tile id) (F.pt ((t' : ℝ) + 1) ((r : ℝ) + ((s - 1 : ℕ) : ℝ)))
            (F.pt (t' : ℝ) (((r : ℝ) + ((s - 1 : ℕ) : ℝ)) + 1))
            (F.pt ((t' : ℝ) + 1) (((r : ℝ) + ((s - 1 : ℕ) : ℝ)) + 1)) := hid
        rw [hy] at hid'
        obtain ⟨k, hk⟩ := hid'.edge_BC
        exact ⟨id, k, by rw [hk]⟩)
      (τ := (n' : ℝ) * (1 - t)) (mul_nonneg hnr.le (by linarith)) (by nlinarith)
    refine ⟨i, k, ?_⟩
    have : AffineMap.lineMap P G t = F.pt ((n' : ℝ) * (1 - t)) ρ := by
      rw [hP, hG', F.pt_lineMap]; congr 1 <;> ring
    rw [this]; exact hik
  have hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap P G t ∉ interior (D.tile i).carrier := by
    intro t ht0 ht1 i
    obtain ⟨j, k, hmem⟩ := hnear t ht0 ht1
    exact D.toDissection.edge_point_not_interior hmem i
  have hint := F.chord_interior hPG hG (by simp; linarith) (by simp; linarith)
  have hnsG : ¬ Straddled D.toDissection (crossL (-F.e0)) (cross (-F.e0) (F.pt 0 ρ)) G :=
    F.ns_end_x (le_refl _) hnr (crossL (-F.e0)) _ hg0 hgP hgG
  have hns' : ¬ Straddled D.toDissection (crossL (-F.e0)) (cross (-F.e0) (F.pt 0 ρ)) P := by
    rw [hP, hn'r]; exact hns
  obtain ⟨-, -, hpos⟩ := far_positions D.toDissection (ta e f) (tb e f) (tc e f) (tc e f) n'
    (fun x y z h => by
      have h' : x * ta e f + y * tb e f + z * tc e f = n' * tc e f := h
      obtain ⟨hx, hy, hz⟩ := MJ_jc_unique e f x y z n' F.S.he F.S.hef F.S.hcop hn'e h'
      exact ⟨Or.inr hx, Or.inr hy, Or.inl rfl⟩)
    (fun i k => w2_habc F.S i k) hne hPGd (by exact_mod_cast (LFrame.tc_pos F.S)) _ _ hg0 hgP hgG hint hwall hns' hnsG
  intro k hk
  have hk' : k < n' := by omega
  obtain ⟨e', he', hends⟩ := hpos k hk'
  refine ⟨e', he', ?_⟩
  have h1 : AffineMap.lineMap P G ((k : ℝ) / n') = F.pt ((m : ℝ) + 1 - s - k) ρ := by
    rw [hP, hG', F.pt_lineMap, ← hn'r]; congr 1 <;> field_simp <;> ring
  have h2 : AffineMap.lineMap P G (((k : ℝ) + 1) / n') = F.pt ((m : ℝ) + 1 - s - k - 1) ρ := by
    rw [hP, hG', F.pt_lineMap, ← hn'r]; congr 1 <;> field_simp <;> ring
  rw [h1, h2] at hends
  exact hends

end LFrame

/-- A far-chain edge with endpoints `A, B` gives a tile with vertices `A, B, Z` lying on the far side. -/
theorem chain_tileVerts {D : Dissection N} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {e' : Fin N × Fin 3}
    (he : e' ∈ D.lineChain g c) {A B : Plane}
    (h : ((D.tile e'.1).pts e'.2 = A ∧ (D.tile e'.1).pts (e'.2 + 1) = B) ∨
      ((D.tile e'.1).pts e'.2 = B ∧ (D.tile e'.1).pts (e'.2 + 1) = A)) :
    TileVerts (D.tile e'.1) A B ((D.tile e'.1).pts (e'.2 + 2)) ∧ ∀ j, g ((D.tile e'.1).pts j) ≤ c := by
  refine ⟨?_, (Dissection.mem_lineChain.mp he).2.2⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨e'.2, Or.inl ⟨h1, h2, rfl⟩⟩
  · have F3 : ∀ k : Fin 3, k + 1 + 1 = k + 2 ∧ k + 1 + 2 = k := by decide
    have e1 := (F3 e'.2).1
    have e2 := (F3 e'.2).2
    exact ⟨e'.2 + 1, Or.inr ⟨h2, (by rw [e1]), (by rw [e2, h1])⟩⟩

namespace LFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : LFrame D e f α β γ p q r)

/-- **The hypotenuse cover.**  The line `l` through `J = (m+1, r)` with direction `u = v − e0` is a wall from `J` to
`D_s = (m+1−s, r+s)` whose near side is the `b`-edges of the up tiles of the standard rows; if no far edge passes
through the ends, the far side is covered by `s` `b`-edges at the lattice positions `D_0, …, D_s`, and every far edge
inside `[J, D_s]` is a `b`-edge. -/
theorem l_cover {H m r s : ℕ} (hB : F.Bnd H) (hrH : r + m + 1 ≤ H) (hme : m + 1 ≤ e)
    (hs1 : 1 ≤ s) (hsm : s ≤ m + 1) (hStd : F.Std r m (s - 1))
    (hnsJ : ¬ F.StrL ((m : ℝ) + 1) (r : ℝ) (F.pt ((m : ℝ) + 1) (r : ℝ)))
    (hnsD : ¬ F.StrL ((m : ℝ) + 1) (r : ℝ) (F.pt ((m : ℝ) + 1 - s) ((r : ℝ) + s))) :
    (∀ e' ∈ D.lineChain (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (r : ℝ))),
        (D.tile e'.1).edge e'.2 ⊆ segment ℝ (F.pt ((m : ℝ) + 1) (r : ℝ))
          (F.pt ((m : ℝ) + 1 - s) ((r : ℝ) + s)) →
        dist ((D.tile e'.1).pts e'.2) ((D.tile e'.1).pts (e'.2 + 1)) = tb e f) ∧
    (∀ e' ∈ D.lineChain (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (r : ℝ))),
        (D.tile e'.1).edge e'.2 ⊆ segment ℝ (F.pt ((m : ℝ) + 1) (r : ℝ))
          (F.pt ((m : ℝ) + 1 - s) ((r : ℝ) + s)) →
        ∃ k : ℕ, k < s ∧
        (((D.tile e'.1).pts e'.2 = F.pt ((m : ℝ) + 1 - k) ((r : ℝ) + k) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.pt ((m : ℝ) + 1 - (k + 1)) ((r : ℝ) + (k + 1))) ∨
         ((D.tile e'.1).pts e'.2 = F.pt ((m : ℝ) + 1 - (k + 1)) ((r : ℝ) + (k + 1)) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.pt ((m : ℝ) + 1 - k) ((r : ℝ) + k)))) ∧
    ∀ k : ℕ, k < s →
      ∃ e' ∈ D.lineChain (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (r : ℝ))),
        (((D.tile e'.1).pts e'.2 = F.pt ((m : ℝ) + 1 - k) ((r : ℝ) + k) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.pt ((m : ℝ) + 1 - (k + 1)) ((r : ℝ) + (k + 1))) ∨
         ((D.tile e'.1).pts e'.2 = F.pt ((m : ℝ) + 1 - (k + 1)) ((r : ℝ) + (k + 1)) ∧
          (D.tile e'.1).pts (e'.2 + 1) = F.pt ((m : ℝ) + 1 - k) ((r : ℝ) + k))) := by
  classical
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsmr : (s : ℝ) ≤ m + 1 := by exact_mod_cast hsm
  have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hHr : (r : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  set J := F.pt ((m : ℝ) + 1) (r : ℝ) with hJ
  set G := F.pt ((m : ℝ) + 1 - s) ((r : ℝ) + s) with hG'
  have hJok : F.LatOK ((m : ℝ) + 1) (r : ℝ) := F.latOK hB (by linarith) hrr (by linarith)
  have hGok : F.LatOK ((m : ℝ) + 1 - s) ((r : ℝ) + s) :=
    F.latOK hB (by linarith) (by linarith) (by linarith)
  have hGdiff : G = J + (s : ℝ) • (F.v - F.e0) := by
    rw [hG', hJ]; simp only [pt]; module
  have hPGd : dist J G = (s : ℝ) * tb e f := by
    rw [hGdiff, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, F.hu,
      Real.norm_of_nonneg (by linarith)]
  have hbpos : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f F.S.he F.S.hef
  have hne : J ≠ G := by
    intro h
    rw [h, dist_self] at hPGd
    have := mul_pos (by linarith : (0 : ℝ) < s) hbpos
    linarith
  have hu0 : F.v - F.e0 ≠ 0 := by
    intro h
    have : ‖F.v - F.e0‖ = 0 := by rw [h, norm_zero]
    rw [F.hu] at this
    linarith
  have hg0 : (crossL (F.v - F.e0) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hu0
    apply eq_zero_of_cross_eq_zero
    intro w
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h
    simpa using this
  have hgP : (crossL (F.v - F.e0) : Plane →ₗ[ℝ] ℝ) J = cross (F.v - F.e0) J := rfl
  have hgG : (crossL (F.v - F.e0) : Plane →ₗ[ℝ] ℝ) G = cross (F.v - F.e0) J := by
    simp only [crossL_apply]
    rw [hGdiff, cross_add_right, cross_smul_right, Erdos634.Geometry.cross_self]; ring
  -- near side: the `b`-edges of the up tiles of rows `r, …, r+s-1`
  have hq : ∀ τ : ℝ, F.pt ((m : ℝ) + 1 - τ) ((r : ℝ) + τ) = J + τ • (F.v - F.e0) := by
    intro τ; rw [hJ]; simp only [pt]; module
  have hnear : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
      AffineMap.lineMap J G t ∈ (D.tile i).edge k := by
    intro t ht0 ht1
    obtain ⟨i, k, hik⟩ := chain_cover D.toDissection (fun τ => F.pt ((m : ℝ) + 1 - τ) ((r : ℝ) + τ)) J
      (F.v - F.e0) hq s hs1
      (by
        intro t' ht'
        obtain ⟨hu, hd⟩ := hStd t' (by omega)
        obtain ⟨id, hid⟩ := hu (m - t') (by omega)
        have hx : ((m - t' : ℕ) : ℝ) = (m : ℝ) - t' := by rw [Nat.cast_sub (by omega)]
        rw [hx] at hid
        have h1 : (m : ℝ) - t' + 1 = (m : ℝ) + 1 - t' := by ring
        have h2 : (r : ℝ) + t' + 1 = (r : ℝ) + ((t' : ℝ) + 1) := by ring
        have h3 : (m : ℝ) + 1 - ((t' : ℝ) + 1) = (m : ℝ) - t' := by ring
        obtain ⟨k, hk⟩ := hid.edge_BC
        refine ⟨id, k, ?_⟩
        simp only []
        rw [h1, h2] at hk
        rw [h3]; exact hk)
      (τ := t * s) (by nlinarith) (by nlinarith)
    refine ⟨i, k, ?_⟩
    have : AffineMap.lineMap J G t = F.pt ((m : ℝ) + 1 - t * s) ((r : ℝ) + t * s) := by
      rw [hJ, hG', F.pt_lineMap]; congr 1 <;> ring
    rw [this]; exact hik
  have hwall : ∀ t : ℝ, 0 < t → t < 1 → ∀ i, AffineMap.lineMap J G t ∉ interior (D.tile i).carrier := by
    intro t ht0 ht1 i
    obtain ⟨j, k, hmem⟩ := hnear t ht0 ht1
    exact D.toDissection.edge_point_not_interior hmem i
  have hint := F.chord_interior hJok hGok (by linarith) (by linarith)
  have hnsJ' : ¬ Straddled D.toDissection (crossL (F.v - F.e0)) (cross (F.v - F.e0) J) J := hnsJ
  have hnsG' : ¬ Straddled D.toDissection (crossL (F.v - F.e0)) (cross (F.v - F.e0) J) G := hnsD
  have hsf : s < f := by have := F.S.hef; omega
  obtain ⟨h1, h1', h2⟩ := far_positions D.toDissection (ta e f) (tb e f) (tc e f) (tb e f) s
    (fun x y z h => by
      have h' : x * ta e f + y * tb e f + z * tc e f = s * tb e f := h
      obtain ⟨hx, hy, hz⟩ := MJ_jb_unique e f x y z s F.S.he F.S.hef F.S.hcop hsf h'
      exact ⟨Or.inr hx, Or.inl rfl, Or.inr hz⟩)
    (fun i k => w2_habc F.S i k) hne hPGd (by exact_mod_cast b_pos e f F.S.he F.S.hef) _ _ hg0 hgP hgG
    hint hwall hnsJ' hnsG'
  have hsne : (s : ℝ) ≠ 0 := by linarith
  have l1 : ∀ k : ℕ, AffineMap.lineMap J G ((k : ℝ) / s) = F.pt ((m : ℝ) + 1 - k) ((r : ℝ) + k) := by
    intro k; rw [hJ, hG', F.pt_lineMap]; congr 1 <;> field_simp <;> ring
  have l2 : ∀ k : ℕ, AffineMap.lineMap J G (((k : ℝ) + 1) / s) =
      F.pt ((m : ℝ) + 1 - (k + 1)) ((r : ℝ) + (k + 1)) := by
    intro k; rw [hJ, hG', F.pt_lineMap]; congr 1 <;> field_simp <;> ring
  refine ⟨h1, ?_, ?_⟩
  · intro e' he' hsub
    obtain ⟨k, hk, hends⟩ := h1' e' he' hsub
    refine ⟨k, hk, ?_⟩
    rw [l1, l2] at hends
    exact hends
  · intro k hk
    obtain ⟨e', he', hends⟩ := h2 k hk
    refine ⟨e', he', ?_⟩
    rw [l1, l2] at hends
    exact hends

end LFrame

end Erdos634.LaczMJ
