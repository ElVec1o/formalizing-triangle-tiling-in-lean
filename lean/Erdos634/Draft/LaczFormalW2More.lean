import Erdos634.Draft.LaczFormalW2Vec

/-!
# Rule W2: small tile lemmas (the `c`-edge with `β` at one end, distinct edge lengths)

Erdős #634, band program, rule W2.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich,
Paliy.  UNAUDITED.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar

variable {N : ℕ}

/-- Two different edges of a tile have different lengths. -/
theorem tile_edges_ne {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k k' : Fin 3) (hkk : k ≠ k') :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) ≠ dist ((D.tile i).pts k') ((D.tile i).pts (k' + 1)) := by
  have F : ∀ k : Fin 3, k ≠ k + 1 ∧ k ≠ k + 2 ∧ k + 1 ≠ k + 2 ∧ k + 1 + 1 = k + 2 ∧ k + 2 + 1 = k := by
    decide
  have hc : ∀ k k' : Fin 3, k ≠ k' → k' = k + 1 ∨ k' = k + 2 := by decide
  obtain ⟨f1, f2, f3, f4, f5⟩ := F k
  rcases hc k k' hkk with rfl | rfl
  · have h := tile_adj_ne S i (k + 1) k (k + 2) f1.symm (by
        intro h; exact f3 (by rw [h]) |>.elim) f2
    rw [dist_comm ((D.tile i).pts k), f4]
    exact h
  · have h := tile_adj_ne S i k (k + 1) (k + 2) f1 f2 f3
    rw [f5, dist_comm ((D.tile i).pts (k + 2)) ((D.tile i).pts k)]
    exact h

/-- A `c`-edge with `β` at one end: the other end has `α`, the third vertex `γ`, and the other sides are `a`, `b`. -/
theorem cbeta_tile {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2)
    (h12 : k1 ≠ k2) (hβ : (D.tile i).localAngle ((D.tile i).pts k0) = β)
    (hc : dist ((D.tile i).pts k0) ((D.tile i).pts k1) = sideOpp D.model 2) :
    dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 0 ∧
    (D.tile i).localAngle ((D.tile i).pts k1) = α ∧ (D.tile i).localAngle ((D.tile i).pts k2) = γ ∧
    dist ((D.tile i).pts k1) ((D.tile i).pts k2) = sideOpp D.model 1 := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hadj := tile_adj_B S i k0 k1 k2 h01 h02 h12 hβ
  have hd2 : dist ((D.tile i).pts k0) ((D.tile i).pts k2) = sideOpp D.model 0 := by
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (h1.symm.trans hc) hac
    · exact h2
  have hang := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i
  have hα1 : (D.tile i).localAngle ((D.tile i).pts k1) = α :=
    (hang k1 k0 k2 h01.symm h12 h02).1 hd2
  have hγ2 : (D.tile i).localAngle ((D.tile i).pts k2) = γ :=
    (hang k2 k0 k1 h02.symm h12.symm h01).2.2 hc
  have hadjA := tile_adj_A S i k1 k0 k2 h01.symm h12 h02 hα1
  refine ⟨hd2, hα1, hγ2, ?_⟩
  rcases hadjA with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso; rw [dist_comm] at h1; exact hbc (h1.symm.trans hc)
  · exact h2


/-- Three distinct vertices of a tile are never collinear. -/
theorem tile_cross_ne (T : Tri) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cross (T.pts b - T.pts a) (T.pts c - T.pts a) ≠ 0 := by
  have hcase : (b = a + 1 ∧ c = a + 2) ∨ (b = a + 2 ∧ c = a + 1) := by
    revert hab hac hbc; revert a b c; decide
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [T.det_cyclic a]; exact T.det_ne_zero
  · rw [cross_swap, T.det_cyclic a]; exact neg_ne_zero.mpr T.det_ne_zero

theorem angle_sum_four (D : Dissection N) {y : Plane} (hy : y ∈ interior D.target.carrier)
    {a b c d : Fin N} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (D.tile a).localAngle y + (D.tile b).localAngle y + (D.tile c).localAngle y + (D.tile d).localAngle y
      ≤ 2 * Real.pi := by
  classical
  have h := angle_sum_le D hy {a, b, c, d}
  rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]), Finset.sum_singleton] at h
  linarith

theorem angle_sum_five (D : Dissection N) {y : Plane} (hy : y ∈ interior D.target.carrier)
    {a b c d g : Fin N} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hag : a ≠ g) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbg : b ≠ g) (hcd : c ≠ d) (hcg : c ≠ g) (hdg : d ≠ g) :
    (D.tile a).localAngle y + (D.tile b).localAngle y + (D.tile c).localAngle y + (D.tile d).localAngle y +
      (D.tile g).localAngle y ≤ 2 * Real.pi := by
  classical
  have h := angle_sum_le D hy {a, b, c, d, g}
  rw [Finset.sum_insert (by simp [hab, hac, had, hag]), Finset.sum_insert (by simp [hbc, hbd, hbg]),
    Finset.sum_insert (by simp [hcd, hcg]), Finset.sum_insert (by simp [hdg]), Finset.sum_singleton] at h
  linarith

/-- A base-token left end other than the corner is in the open base. -/
theorem basetok_left_open {D : CongruentDissection N} {p q : Fin 3} {ang : Corner → ℝ} {len : Side → ℝ}
    {x : Side} {l rr : Corner} {i : Fin N} {X Y Z : Plane}
    (hne : D.target.pts p ≠ D.target.pts q)
    (h : BaseTok D p q ang len x l rr i X Y Z) (hX : X ≠ D.target.pts p) :
    X ∈ openSegment ℝ (D.target.pts p) (D.target.pts q) := by
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  have hw : RC - LC ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hwn : 0 < ‖RC - LC‖ := norm_pos_iff.mpr hw
  obtain ⟨sx, hsx0, hsx1, hX'⟩ := seg_param_of_mem h.left_mem
  obtain ⟨sy, hsy0, hsy1, hY'⟩ := seg_param_of_mem h.right_mem
  have hlt : sx < sy := by
    have := h.order
    rw [hX', hY', dist_param_left _ _ hsx0, dist_param_left _ _ hsy0] at this
    by_contra hh; push_neg at hh
    nlinarith
  have hsx0' : 0 < sx := by
    rcases hsx0.eq_or_lt with h0 | h0
    · exfalso; apply hX; rw [hX', ← h0]; simp [hLC]
    · exact h0
  have hsx1' : sx < 1 := by linarith
  rw [hX']
  exact mem_open_param hsx0' hsx1'

/-- A tile edge on the line `{cross u · = cross u P}` containing `P + t0 • u` in its relative interior: its endpoints
are `P + s • u`, `P + s' • u` with `s < t0 < s'` (or reversed). -/
theorem straddle_param {D : Dissection N} {P u : Plane} (hu : u ≠ 0) {t0 : ℝ} {c : ℝ}
    (hc : c = cross u P) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain (crossL u) c)
    (hy : P + t0 • u ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) :
    ∃ sX sY : ℝ, (D.tile e.1).pts e.2 = P + sX • u ∧ (D.tile e.1).pts (e.2 + 1) = P + sY • u ∧
      ((sX < t0 ∧ t0 < sY) ∨ (sY < t0 ∧ t0 < sX)) := by
  obtain ⟨a', b', ha', hb', hab', hV⟩ := hy
  obtain ⟨hX, hY, -⟩ := Dissection.mem_lineChain.mp he
  simp only [crossL_apply] at hX hY
  set X := (D.tile e.1).pts e.2 with hXdef
  set Y := (D.tile e.1).pts (e.2 + 1) with hYdef
  have cX : cross u (X - P) = 0 := by rw [cross_sub_right]; linarith
  have cY : cross u (Y - P) = 0 := by rw [cross_sub_right]; linarith
  obtain ⟨sX, hsX⟩ := on_line_param hu cX
  obtain ⟨sY, hsY⟩ := on_line_param hu cY
  have hXe : X = P + sX • u := by rw [← hsX]; abel
  have hYe : Y = P + sY • u := by rw [← hsY]; abel
  have hXY : X ≠ Y := by
    intro h
    have : e.2 = e.2 + 1 := (D.tile e.1).indep.injective h
    exact (by decide : ∀ k : Fin 3, k ≠ k + 1) e.2 this
  have hsne : sX ≠ sY := by
    intro h; apply hXY; rw [hXe, hYe, h]
  have h1 : t0 = a' * sX + b' * sY := by
    have : t0 • u = (a' * sX + b' * sY) • u := by
      have e1 : P + t0 • u = P + (a' * sX + b' * sY) • u := by
        rw [← hV, hXe, hYe]
        have : P = (a' + b') • P := by rw [hab', one_smul]
        calc a' • (P + sX • u) + b' • (P + sY • u) = (a' + b') • P + (a' * sX + b' * sY) • u := by module
          _ = P + (a' * sX + b' * sY) • u := by rw [hab', one_smul]
      exact add_left_cancel e1
    exact smul_injective_of_ne hu this
  refine ⟨sX, sY, hXe, hYe, ?_⟩
  have ea : a' = 1 - b' := by linarith
  have eb : b' = 1 - a' := by linarith
  have h1' : t0 = sX + b' * (sY - sX) := by rw [h1, ea]; ring
  have h1'' : t0 = sY - a' * (sY - sX) := by rw [h1, eb]; ring
  rcases lt_or_gt_of_ne hsne with hl | hl
  · left
    have p1 := mul_pos hb' (sub_pos.mpr hl)
    have p2 := mul_pos ha' (sub_pos.mpr hl)
    constructor <;> linarith
  · right
    have p1 := mul_pos hb' (sub_pos.mpr hl)
    have p2 := mul_pos ha' (sub_pos.mpr hl)
    constructor <;> nlinarith

end Erdos634.LaczJunction.Walk
