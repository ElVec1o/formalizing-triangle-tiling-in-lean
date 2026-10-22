/-
Draft/SideRunRow.lean -- Stage 3a of the formalization of the side theorem of room GAP3: the statement `K(s, j0)`
and Lemma Row ((private working notes, not included), sections 1-2).

* `K2 s j0`: the rows `≤ j0` of the triangle `Δ_s` are lattice; `Aprop m`: the claim `K(s, j0)` for all pairs with
  `s − j0 = m` (under the standing hypotheses `Ctx`, which contain (K1));
* `Ctx.row_step`: the tile above a row at `p(ρ, ζ+1)`, next to the `c`-edge of `D(ρ, ζ)`: it is `U(ρ, ζ+1)`, or it
  shows `β` or `γ` at `p(ρ, ζ+1)` (the edges on a clamped row of length `q c`, `q < n`, are `a`- and `c`-edges);
* `Ctx.row_bad0`: the second alternative is impossible at `ρ = 0` (angles at `p(0, ζ+1)`, with the tile `φ`);
* `Ctx.row_bad`: it is impossible at `ρ ≥ 1` if no tile gives (K3) for the run `(ρ+ζ+1, ζ+1)`
  (six tiles at `p(ρ, ζ+1)` and `3α < β`);
* `Ctx.row`: **Lemma Row**.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunChord

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.W2E1 Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay ε x : ℝ}

theorem HasV.congr {t : Fin N} {A B C A' B' C' : Plane} (h : HasV D t A B C) (hA : A = A')
    (hB : B = B') (hC : C = C') : HasV D t A' B' C' := by
  subst hA; subst hB; subst hC; exact h

theorem HasV.idx₁ {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    ∃ i, (D.tile t).pts i = A := by
  obtain ⟨k, m, j, -, -, -, hk, -, -⟩ := h
  exact ⟨k, hk⟩

theorem HasV.idx₂ {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    ∃ i, (D.tile t).pts i = B := by
  obtain ⟨k, m, j, -, -, -, -, hm, -⟩ := h
  exact ⟨m, hm⟩

theorem HasV.idx₃ {t : Fin N} {A B C : Plane} (h : HasV D t A B C) :
    ∃ i, (D.tile t).pts i = C := by
  obtain ⟨k, m, j, -, -, -, -, -, hj⟩ := h
  exact ⟨j, hj⟩

/-- **(K2)**: the rows `≤ j0` of `Δ_s` are lattice. -/
def K2 (D : CongruentDissection N) (n ε x : ℝ) (s j0 : ℕ) : Prop :=
  (∀ i j : ℕ, j ≤ j0 → i + j + 1 ≤ s → UT D n ε x i j) ∧
  (∀ i j : ℕ, j < j0 → i + j + 2 ≤ s → DT D n ε x i j)

/-- **The claim `K(s, j0)` for all pairs of size `m`**: (K2) and (K3) are contradictory. -/
def Aprop (D : CongruentDissection N) (n : ℕ) (ε x : ℝ) (m : ℕ) : Prop :=
  ∀ s j0 : ℕ, j0 < s → s < n → s - j0 = m → K2 D n ε x s j0 → K3 D n ε x s j0 → False

theorem GS_le {n' ε' x' a b s : ℝ} (hn : 1 < n') (hε : ε' ^ 2 = 1) (h : s ≤ a + b) :
    GS n' ε' (lp n' ε' x' a b) ≤ -lv n' ε' x' s := by
  rw [GS_lp hε]; exact neg_le_neg (lv_le hn h)

theorem GS_gt {n' ε' x' a b s : ℝ} (hn : 1 < n') (hε : ε' ^ 2 = 1) (h : a + b < s) :
    -lv n' ε' x' s < GS n' ε' (lp n' ε' x' a b) := by
  rw [GS_lp hε]; exact neg_lt_neg (lv_lt hn h)

theorem GH_le {n' ε' x' a b η : ℝ} (hn : 1 < n') (h : η ≤ b) :
    GH n' (lp n' ε' x' a b) ≤ -(n' ^ 2 * hh n' * η) := by
  rw [GH_lp]; exact neg_le_neg (mul_le_mul_of_nonneg_left h (nh_pos hn).le)

theorem GH_gt {n' ε' x' a b η : ℝ} (hn : 1 < n') (h : b < η) :
    -(n' ^ 2 * hh n' * η) < GH n' (lp n' ε' x' a b) := by
  rw [GH_lp]; exact neg_lt_neg (mul_lt_mul_of_pos_left h (nh_pos hn))

namespace Ctx

/-- **The tile above a row** at `p(ρ, ζ+1)`, next to the `c`-edge of `D(ρ, ζ)`. -/
theorem row_step (C : Ctx D n α β γ L ax ay ε x) {ρ ζ : ℝ} {tD : Fin N}
    (hDt : HasV D tD (lp n ε x (ρ + 1) ζ) (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)))
    (hζ : 0 ≤ ζ)
    (hcl : ∃ P' : Plane, GH n P' = -((n:ℝ) ^ 2 * hh n * (ζ + 1)) ∧
      lp n ε x ρ (ζ + 1) ∈ openSegment ℝ P' (lp n ε x (ρ + 1) (ζ + 1)) ∧
      ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * (ζ + 1))),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)))
    (hnob : ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * (ζ + 1))),
      (D.tile e.1).edge e.2 ⊆ segment ℝ (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)) →
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ (n:ℝ) ^ 2 - 1) :
    UT D n ε x ρ (ζ + 1) ∨
    ∃ (ix : Fin N) (k m j₃ : Fin 3) (t : ℝ), k ≠ m ∧ k ≠ j₃ ∧ m ≠ j₃ ∧
      (D.tile ix).pts k = lp n ε x ρ (ζ + 1) ∧ 0 < t ∧ (D.tile ix).pts m = lp n ε x (ρ + t) (ζ + 1) ∧
      (∀ i, GH n ((D.tile ix).pts i) ≤ -((n:ℝ) ^ 2 * hh n * (ζ + 1))) ∧
      ((D.tile ix).localAngle (lp n ε x ρ (ζ + 1)) = β ∨
        (D.tile ix).localAngle (lp n ε x ρ (ζ + 1)) = γ) ∧
      (∀ i, (D.tile ix).pts i = lp n ε x (ρ - 1) (ζ + 1 + 1) → False) := by
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  have hf0 := S.f0
  have hf2 := S.f2
  have hc := S.c_pos
  have hVW : lp n ε x ρ (ζ + 1) ≠ lp n ε x (ρ + 1) (ζ + 1) := lp_ne_xi hf1 hε (by linarith)
  have hfV : GH n (lp n ε x ρ (ζ + 1)) = -((n:ℝ) ^ 2 * hh n * (ζ + 1)) := GH_lp _ _ _ _ _
  have hfW : GH n (lp n ε x (ρ + 1) (ζ + 1)) = -((n:ℝ) ^ 2 * hh n * (ζ + 1)) := GH_lp _ _ _ _ _
  have hint : openSegment ℝ (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1))
      ⊆ interior D.target.carrier := by
    refine C.seg_int hDt.mem₂ hDt.mem₃ (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hDt.mem₃⟩)
      (Or.inr ⟨1, one_pos, ?_⟩)
    rw [show ρ + 1 - 1 = ρ by ring]; exact hDt.mem₂
  have hwall : ∀ y ∈ openSegment ℝ (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hDt
    refine seg_wall D.toDissection (t := tD) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨P', hfP', hP', hP⟩ := hcl
  obtain ⟨e, he, k, m, t, hkm, hk, ht, hm0, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GH n) (GH_ne hf1) _ hVW hfV hfW hfP' hP' hint hwall hP
  have hm : (D.tile e.1).pts m = lp n ε x (ρ + t) (ζ + 1) := by
    rw [hm0, lineMap_lp]; exact lp_congr (by ring) (by ring)
  have hd : dist ((D.tile e.1).pts k) ((D.tile e.1).pts m) = t * (n:ℝ) ^ 2 := by
    rw [hk, hm]
    exact dist_lp hf1 hε (by positivity) (by unfold Qf; ring)
  have hlam := vertex_dist_cases D S.hM e.1 hkm
  have hnn2 : (n:ℝ) < (n:ℝ) ^ 2 - 1 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (n:ℝ) - 2 by linarith) hf0.le]
  have hc4 : (4:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
  have ht1 : t ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h1 : (n:ℝ) ^ 2 < t * (n:ℝ) ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hgt) hc]
    rcases hlam with h | h | h <;> rw [hd] at h <;> linarith
  have hsub : (D.tile e.1).edge e.2
      ⊆ segment ℝ (lp n ε x ρ (ζ + 1)) (lp n ε x (ρ + 1) (ζ + 1)) := by
    rw [hedge]
    refine (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) ?_
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩
  have hlamb : dist ((D.tile e.1).pts k) ((D.tile e.1).pts m) ≠ (n:ℝ) ^ 2 - 1 := by
    have h1 := hnob e he hsub
    rw [hdist] at h1
    rw [hk, hm0]; exact h1
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j₃ := Ne.symm hjk
  have hmj : m ≠ j₃ := Ne.symm hjm
  have hGV : dist (lp n ε x (ρ - 1) (ζ + 1 + 1)) (lp n ε x ρ (ζ + 1)) = n :=
    dist_lp hf1 hε hf0.le (by unfold Qf; ring)
  have hGW : dist (lp n ε x (ρ - 1) (ζ + 1 + 1)) (lp n ε x (ρ + 1) (ζ + 1)) ^ 2
      = (n:ℝ) ^ 4 + 4 * (n:ℝ) ^ 2 - 1 := by
    rw [dist_lp_sq hf1 hε]; unfold Qf; ring
  have hA := angle_at_vertex D hf2 S.hM e.1 hkm hkj hmj
  rw [hk] at hA
  -- the common part of "the vertex `p(ρ−1, ζ+2)` is not a vertex of the tile"
  have hno_km : ∀ i, i = k ∨ i = m → (D.tile e.1).pts i = lp n ε x (ρ - 1) (ζ + 1 + 1) → False := by
    intro i hi hpi
    rcases hi with rfl | rfl
    · rw [hk] at hpi
      have := lp_eta_eq hf1 hpi
      linarith
    · rw [hm] at hpi
      have := lp_eta_eq hf1 hpi
      linarith
  rcases hlam with h | h | h
  · -- an `a`-edge
    right
    rcases sides_of_a_edge D hf2 S.hM e.1 hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · refine ⟨e.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inl (hA.2.1 (by rw [dist_comm]; exact s2)), fun i hpi => ?_⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hk, hGV] at s1
        linarith
    · refine ⟨e.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inr (hA.2.2 (by rw [dist_comm]; exact s2)), fun i hpi => ?_⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hk, hGV] at s1
        linarith
  · exact absurd h hlamb
  · -- a `c`-edge
    have ht1' : t = 1 := by
      have h1 : t * (n:ℝ) ^ 2 = 1 * (n:ℝ) ^ 2 := by rw [one_mul, ← hd, h]
      exact mul_right_cancel₀ hc.ne' h1
    have hmW : (D.tile e.1).pts m = lp n ε x (ρ + 1) (ζ + 1) := by rw [hm, ht1']
    rcases sides_of_c_edge D hf2 S.hM e.1 hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · right
      refine ⟨e.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inl (hA.2.1 (by rw [dist_comm]; exact s2)), fun i hpi => ?_⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hmW] at s2
        rw [s2] at hGW
        nlinarith
    · left
      exact ⟨e.1, row_edge_U S hε hkm hkj hmj hk hmW hle s1 s2⟩

/-- **The tile above the row at `p(0, ζ+1)` shows less than `β`**: angles of `φ`, `U(0,ζ)`, `D(0,ζ)`. -/
theorem row_bad0 (C : Ctx D n α β γ L ax ay ε x) {ζ : ℝ} {φ tU tD ix : Fin N}
    (hφπ : (D.tile φ).localAngle (lp n ε x 0 (ζ + 1)) = Real.pi)
    (hU : HasV D tU (lp n ε x 0 ζ) (lp n ε x (0 + 1) ζ) (lp n ε x 0 (ζ + 1)))
    (hDt : HasV D tD (lp n ε x (0 + 1) ζ) (lp n ε x 0 (ζ + 1)) (lp n ε x (0 + 1) (ζ + 1)))
    (hle : ∀ i, GH n ((D.tile ix).pts i) ≤ -((n:ℝ) ^ 2 * hh n * (ζ + 1)))
    (hθ : (D.tile ix).localAngle (lp n ε x 0 (ζ + 1)) = β ∨
      (D.tile ix).localAngle (lp n ε x 0 (ζ + 1)) = γ) : False := by
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ := S.alpha_lt_beta
  have hγdef := S.hA.hγdef
  have hβπ : β < Real.pi := by linarith
  have hβγ : β < γ := by linarith
  have hUγ := (U_angles S hε hU).2.2
  have hDβ := (D_angles S hε hDt).2.1
  have hφU : φ ≠ tU := ne_of_angle (by rw [hφπ, hUγ]; exact hγπ.ne')
  have hφD : φ ≠ tD := ne_of_angle (by rw [hφπ, hDβ]; exact hβπ.ne')
  have hφx : φ ≠ ix := by
    rcases hθ with h | h
    · exact ne_of_angle (by rw [hφπ, h]; exact hβπ.ne')
    · exact ne_of_angle (by rw [hφπ, h]; exact hγπ.ne')
  have hUD : tU ≠ tD := ne_of_angle (by rw [hUγ, hDβ]; exact hβγ.ne')
  have hxU : ix ≠ tU := by
    obtain ⟨k, hk⟩ := hU.idx₁
    exact ne_of_F (GH n) hle (i := k) (by rw [hk]; exact GH_gt hf1 (by linarith))
  have hxD : ix ≠ tD := by
    obtain ⟨k, hk⟩ := hDt.idx₁
    exact ne_of_F (GH n) hle (i := k) (by rw [hk]; exact GH_gt hf1 (by linarith))
  have h4 := four_angles_le D.toDissection (lp n ε x 0 (ζ + 1)) hφU hφD hφx hUD (Ne.symm hxU)
    (Ne.symm hxD)
  have h2π := localAngle_le_two_pi D.target (lp n ε x 0 (ζ + 1))
  rw [hφπ, hUγ, hDβ] at h4
  rcases hθ with h | h <;> rw [h] at h4 <;> linarith

/-- six tiles at `p(ξ+1, ζ+1)`: `D(ξ,ζ)`, `U(ξ+1,ζ)`, `D(ξ+1,ζ)`, `U(ξ,ζ+1)`, the tile above the row and the tile
across the `a`-edge of `U(ξ,ζ+1)`, the last two showing at least `β` -/
theorem row_six (C : Ctx D n α β γ L ax ay ε x) (hn3 : 3 ≤ n) {ξ ζ : ℝ}
    {t₁ t₂ t₃ t₄ ix t₆ : Fin N}
    (h1 : HasV D t₁ (lp n ε x (ξ + 1) ζ) (lp n ε x ξ (ζ + 1)) (lp n ε x (ξ + 1) (ζ + 1)))
    (h2 : HasV D t₂ (lp n ε x (ξ + 1) ζ) (lp n ε x (ξ + 1 + 1) ζ) (lp n ε x (ξ + 1) (ζ + 1)))
    (h3 : HasV D t₃ (lp n ε x (ξ + 1 + 1) ζ) (lp n ε x (ξ + 1) (ζ + 1))
      (lp n ε x (ξ + 1 + 1) (ζ + 1)))
    (h4 : HasV D t₄ (lp n ε x ξ (ζ + 1)) (lp n ε x (ξ + 1) (ζ + 1)) (lp n ε x ξ (ζ + 1 + 1)))
    {m : Fin 3} {t : ℝ} (ht : 0 < t) (hm : (D.tile ix).pts m = lp n ε x (ξ + 1 + t) (ζ + 1))
    (hle : ∀ i, GH n ((D.tile ix).pts i) ≤ -((n:ℝ) ^ 2 * hh n * (ζ + 1)))
    (hθ : (D.tile ix).localAngle (lp n ε x (ξ + 1) (ζ + 1)) = β ∨
      (D.tile ix).localAngle (lp n ε x (ξ + 1) (ζ + 1)) = γ)
    (hno : ∀ i, (D.tile ix).pts i = lp n ε x ξ (ζ + 1 + 1) → False) {X : Plane}
    (h6 : HasV D t₆ (lp n ε x (ξ + 1) (ζ + 1)) (lp n ε x ξ (ζ + 1 + 1)) X)
    (hθ' : (D.tile t₆).localAngle (lp n ε x (ξ + 1) (ζ + 1)) = β ∨
      (D.tile t₆).localAngle (lp n ε x (ξ + 1) (ζ + 1)) = γ)
    (hle6 : ∀ i, GS n ε ((D.tile t₆).pts i) ≤ -lv n ε x (ξ + (ζ + 1) + 1)) : False := by
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ := S.alpha_lt_beta
  have h3αβ := S.three_alpha_lt_beta hn3
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hβγ : β < γ := by linarith
  have hαγ : α < γ := by linarith
  have a1 := (D_angles S hε h1).2.2
  have a2 := (U_angles S hε h2).2.2
  have a3 := (D_angles S hε h3).2.1
  have a4 := (U_angles S hε h4).2.1
  have n12 : t₁ ≠ t₂ := ne_of_angle (by rw [a1, a2]; exact hαγ.ne)
  have n13 : t₁ ≠ t₃ := ne_of_angle (by rw [a1, a3]; exact hαβ.ne)
  have n14 : t₁ ≠ t₄ := ne_of_angle (by rw [a1, a4]; exact hαβ.ne)
  have n15 : t₁ ≠ ix := by
    rcases hθ with h | h
    · exact ne_of_angle (by rw [a1, h]; exact hαβ.ne)
    · exact ne_of_angle (by rw [a1, h]; exact hαγ.ne)
  have n16 : t₁ ≠ t₆ := by
    rcases hθ' with h | h
    · exact ne_of_angle (by rw [a1, h]; exact hαβ.ne)
    · exact ne_of_angle (by rw [a1, h]; exact hαγ.ne)
  have n23 : t₂ ≠ t₃ := ne_of_angle (by rw [a2, a3]; exact hβγ.ne')
  have n24 : t₂ ≠ t₄ := ne_of_angle (by rw [a2, a4]; exact hβγ.ne')
  have n25 : t₂ ≠ ix := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GH n) hle (i := k) (by rw [hk]; exact GH_gt hf1 (by linarith))).symm
  have n26 : t₂ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GS n ε) hle6 (i := k) (by rw [hk]; exact GS_gt hf1 hε (by linarith))).symm
  have hle3 := h3.all (P := fun p => GS n ε p ≤ -lv n ε x (ξ + (ζ + 1) + 1))
    (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
  have n34 : t₃ ≠ t₄ := by
    obtain ⟨k, hk⟩ := h4.idx₁
    exact ne_of_F (GS n ε) hle3 (i := k) (by rw [hk]; exact GS_gt hf1 hε (by linarith))
  have n35 : t₃ ≠ ix := by
    obtain ⟨k, hk⟩ := h3.idx₁
    exact (ne_of_F (GH n) hle (i := k) (by rw [hk]; exact GH_gt hf1 (by linarith))).symm
  have n36 : t₃ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h6.idx₂
    exact (h3.ne_of_vertex hk (lp_ne_eta hf1 (by linarith)) (lp_ne_eta hf1 (by linarith))
      (lp_ne_eta hf1 (by linarith))).symm
  have n45 : t₄ ≠ ix :=
    (h4.ne_of_vertex hm (lp_ne_xi hf1 hε (by linarith)) (lp_ne_xi hf1 hε (by linarith))
      (lp_ne_eta hf1 (by linarith))).symm
  have n46 : t₄ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h4.idx₁
    exact (ne_of_F (GS n ε) hle6 (i := k) (by rw [hk]; exact GS_gt hf1 hε (by linarith))).symm
  have n56 : ix ≠ t₆ := by
    rintro rfl
    obtain ⟨k, hk⟩ := h6.idx₂
    exact hno k hk
  have h6' := six_angles_le D.toDissection (lp n ε x (ξ + 1) (ζ + 1)) n12 n13 n14 n15 n16 n23 n24
    n25 n26 n34 n35 n36 n45 n46 n56
  have h2π := localAngle_le_two_pi D.target (lp n ε x (ξ + 1) (ζ + 1))
  rw [a1, a2, a3, a4] at h6'
  rcases hθ with h | h <;> rcases hθ' with h' | h' <;> rw [h, h'] at h6' <;> linarith

/-- **The tile above the row at `p(ξ+1, ζ+1)` shows less than `β`** if no tile gives (K3) for the run
`(ξ+ζ+2, ζ+1)`. -/
theorem row_bad (C : Ctx D n α β γ L ax ay ε x) (hn3 : 3 ≤ n) {ξ ζ : ℝ} (hζ : 0 ≤ ζ)
    {t₁ t₂ t₃ t₄ ix : Fin N}
    (h1 : HasV D t₁ (lp n ε x (ξ + 1) ζ) (lp n ε x ξ (ζ + 1)) (lp n ε x (ξ + 1) (ζ + 1)))
    (h2 : HasV D t₂ (lp n ε x (ξ + 1) ζ) (lp n ε x (ξ + 1 + 1) ζ) (lp n ε x (ξ + 1) (ζ + 1)))
    (h3 : HasV D t₃ (lp n ε x (ξ + 1 + 1) ζ) (lp n ε x (ξ + 1) (ζ + 1))
      (lp n ε x (ξ + 1 + 1) (ζ + 1)))
    (h4 : HasV D t₄ (lp n ε x ξ (ζ + 1)) (lp n ε x (ξ + 1) (ζ + 1)) (lp n ε x ξ (ζ + 1 + 1)))
    {m : Fin 3} {t : ℝ} (ht : 0 < t) (hm : (D.tile ix).pts m = lp n ε x (ξ + 1 + t) (ζ + 1))
    (hle : ∀ i, GH n ((D.tile ix).pts i) ≤ -((n:ℝ) ^ 2 * hh n * (ζ + 1)))
    (hθ : (D.tile ix).localAngle (lp n ε x (ξ + 1) (ζ + 1)) = β ∨
      (D.tile ix).localAngle (lp n ε x (ξ + 1) (ζ + 1)) = γ)
    (hno : ∀ i, (D.tile ix).pts i = lp n ε x ξ (ζ + 1 + 1) → False) (hb : ξ + 2 ≤ n)
    (hRho : ∀ w, RhoEdge D n ε x w (ξ + (ζ + 1) + 1) (ζ + 1) → False) : False := by
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  have hν0 := nu_pos hf1
  -- the tile `S'` across the `a`-edge of `U(ξ, ζ+1)`
  have hcl : ∃ P' : Plane, GS n ε P' = -lv n ε x (ξ + (ζ + 1) + 1) ∧
      lp n ε x (ξ + 1) (ζ + 1) ∈ openSegment ℝ P' (lp n ε x ξ (ζ + 1 + 1)) ∧
      ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x (ξ + (ζ + 1) + 1)),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x (ξ + 1) (ζ + 1))
          (lp n ε x ξ (ζ + 1 + 1)) := by
    have hle3 := h3.all (P := fun p => GS n ε p ≤ -lv n ε x (ξ + (ζ + 1) + 1))
      (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
    obtain ⟨k, m', j, hkm, hkj, hmj, hk, hm', hj⟩ := h3
    exact C.m_clamp_tile hkm (by rw [hk]; exact lp_congr (by ring) (by ring)) hm' hle3
  rcases C.m_next h4 (by linarith) ⟨1, one_pos, h3.mem₃⟩ hcl hb with ⟨t₆, h6⟩ | ⟨t₆, h6⟩ | ⟨w, hw⟩
  · -- `S' = D(ξ, ζ+1)` shows `γ`
    exact C.row_six hn3 h1 h2 h3 h4 ht hm hle hθ hno h6 (Or.inr (D_angles S hε h6).1)
      (h6.all (P := fun p => GS n ε p ≤ -lv n ε x (ξ + (ζ + 1) + 1)) (GS_le hf1 hε (by linarith))
        (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)))
  · -- `S' = N(ξ, ζ+1)` shows `β`
    exact C.row_six hn3 h1 h2 h3 h4 ht hm hle hθ hno h6 (Or.inl (N_angles S hε h6).1)
      (h6.all (P := fun p => GS n ε p ≤ -lv n ε x (ξ + (ζ + 1) + 1)) (GS_le hf1 hε (by linarith))
        (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)))
  · exact hRho w hw

/-- **LEMMA ROW.**  Let the rows `≤ j` of `Δ_{q+j+1}` be lattice, `D(0,j), …, D(q−1,j)` be tiles, the right end of
the row segment `[p(0,j+1), p(q,j+1)]` be clamped for the tiles above it, and the claim hold for the sizes `< q`.
Then `U(0,j+1), …, U(q−1,j+1)` are tiles. -/
theorem row (C : Ctx D n α β γ L ax ay ε x) (hn3 : 3 ≤ n) {j q : ℕ} (hq : 1 ≤ q)
    (hqj : q + j + 2 ≤ n)
    (hUr : ∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ q + j → UT D n ε x i' j')
    (hDr : ∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ q + j → DT D n ε x i' j')
    (hD : ∀ i' : ℕ, i' < q → DT D n ε x i' j)
    (hcl : ∃ Q' : Plane, GH n Q' = -((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1)) ∧
      lp n ε x q ((j:ℝ) + 1) ∈ openSegment ℝ (lp n ε x 0 ((j:ℝ) + 1)) Q' ∧
      ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1))),
        ¬ Straddles ((D.tile e.1).edge e.2) Q' (lp n ε x q ((j:ℝ) + 1)) (lp n ε x 0 ((j:ℝ) + 1)))
    (hA : ∀ m' : ℕ, 1 ≤ m' → m' < q → Aprop D n ε x m') :
    ∀ r : ℕ, r < q → UT D n ε x r ((j:ℝ) + 1) := by
  classical
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  have hf0 := S.f0
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  -- the tile `φ_j` at `p(0, j+1)`
  obtain ⟨φ, hφc, hφπ, hφpush⟩ := C.phi (j := j + 1) (by omega) (by omega)
    (fun j' hj' => by
      have h := hUr 0 j' (by omega) (by omega)
      rwa [Nat.cast_zero] at h)
  simp only [Nat.cast_add, Nat.cast_one] at hφc hφπ hφpush
  -- the row segment
  have hA0q : lp n ε x 0 ((j:ℝ) + 1) ≠ lp n ε x q ((j:ℝ) + 1) := lp_ne_xi hf1 hε hqpos.ne
  have hfA0 : GH n (lp n ε x 0 ((j:ℝ) + 1)) = -((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1)) := GH_lp _ _ _ _ _
  have hfAq : GH n (lp n ε x q ((j:ℝ) + 1)) = -((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1)) := GH_lp _ _ _ _ _
  have hdir : FX n ε (lp n ε x 0 ((j:ℝ) + 1) - lp n ε x q ((j:ℝ) + 1)) < 0 := by
    rw [map_sub, FX_lp hε, FX_lp hε]
    linarith [lv_lt (n := (n:ℝ)) (ε := ε) (x := x) hf1 hqpos]
  obtain ⟨P', hfP', hP', hsubφ⟩ := ext_point_of_push (GH n) hfA0 hfAq hφc (hφpush _ hdir)
  obtain ⟨tD0, hD0⟩ := hD 0 (by omega)
  rw [Nat.cast_zero] at hD0
  obtain ⟨tDq, hDq⟩ := hD (q - 1) (by omega)
  have hcq : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by rw [Nat.cast_sub hq, Nat.cast_one]
  rw [hcq] at hDq
  have hAq_mem : lp n ε x q ((j:ℝ) + 1) ∈ D.target.carrier := by
    have := hDq.mem₃
    rwa [show (q:ℝ) - 1 + 1 = q by ring] at this
  have hint : openSegment ℝ (lp n ε x 0 ((j:ℝ) + 1)) (lp n ε x q ((j:ℝ) + 1))
      ⊆ interior D.target.carrier :=
    C.seg_int hD0.mem₂ hAq_mem (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hD0.mem₃⟩)
      (Or.inr ⟨1, one_pos, hDq.mem₂⟩)
  have hwall : ∀ y ∈ openSegment ℝ (lp n ε x 0 ((j:ℝ) + 1)) (lp n ε x q ((j:ℝ) + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lp n ε x 0 ((j:ℝ) + 1))
        (lp n ε x (0 + (q:ℝ) * 1) ((j:ℝ) + 1 + (q:ℝ) * 0)) := by
      rw [show lp n ε x (0 + (q:ℝ) * 1) ((j:ℝ) + 1 + (q:ℝ) * 0) = lp n ε x q ((j:ℝ) + 1) from
        lp_congr (by ring) (by ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i', hi', hyi⟩ := seg_split_lp hq hy'
    obtain ⟨t, k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hD i' hi'
    refine seg_wall D.toDissection (t := t) hmj ?_
    rw [hm, hj]
    rw [show lp n ε x (0 + (i':ℝ) * 1) ((j:ℝ) + 1 + (i':ℝ) * 0) = lp n ε x i' ((j:ℝ) + 1) from
      lp_congr (by ring) (by ring),
      show lp n ε x (0 + ((i':ℝ) + 1) * 1) ((j:ℝ) + 1 + ((i':ℝ) + 1) * 0)
        = lp n ε x ((i':ℝ) + 1) ((j:ℝ) + 1) from lp_congr (by ring) (by ring)] at hyi
    exact hyi
  obtain ⟨Q', hfQ', hQ', hQc⟩ := hcl
  have hpart := run_partition D.toDissection (GH n) (GH_ne hf1) _ hA0q hfP' hfQ' hP' hQ'
    (CSlot.segment_subset_level (GH n) _ hfA0 hfAq) hint hwall
    (fun e _ => not_straddles_of_interior D.toDissection hsubφ e.1 e.2) hQc
  have hdq : dist (lp n ε x 0 ((j:ℝ) + 1)) (lp n ε x q ((j:ℝ) + 1)) = (q:ℝ) * (n:ℝ) ^ 2 :=
    dist_lp hf1 hε (by positivity) (by unfold Qf; ring)
  have hnobΛ : ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1))),
      (D.tile e.1).edge e.2 ⊆ segment ℝ (lp n ε x 0 ((j:ℝ) + 1)) (lp n ε x q ((j:ℝ) + 1)) →
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ (n:ℝ) ^ 2 - 1 := by
    intro e he hsub
    obtain ⟨x', y', z', hxyz⟩ := sum_split_semigroup _ _ (n:ℝ) ((n:ℝ) ^ 2 - 1) ((n:ℝ) ^ 2) _
      (fun e' _ => edge_length_cases D S.hM e'.1 e'.2) (Finset.mem_filter.mpr ⟨he, hsub⟩) hpart
    rw [hdq] at hxyz
    exact first_len_qc S.hn2 (by omega) hxyz
  have hrowmem : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ q →
      lp n ε x ρ ((j:ℝ) + 1) ∈ segment ℝ (lp n ε x 0 ((j:ℝ) + 1)) (lp n ε x q ((j:ℝ) + 1)) := by
    intro ρ h0 h1
    have h := lp_mem_seg (n := n) (ε := ε) (x := x) (ξ := 0) (η := (j:ℝ) + 1) (ξ' := q)
      (η' := (j:ℝ) + 1) (τ := ρ / q) (div_nonneg h0 hqpos.le) (by rw [div_le_one hqpos]; exact h1)
    rw [show lp n ε x (0 + ρ / (q:ℝ) * ((q:ℝ) - 0)) ((j:ℝ) + 1 + ρ / (q:ℝ) * ((j:ℝ) + 1 - ((j:ℝ) + 1)))
        = lp n ε x ρ ((j:ℝ) + 1) from
      lp_congr (by rw [sub_zero, div_mul_cancel₀ _ hqpos.ne', zero_add]) (by ring)] at h
    exact h
  have hnobstep : ∀ ρ : ℝ, 0 ≤ ρ → ρ + 1 ≤ q →
      ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1))),
      (D.tile e.1).edge e.2 ⊆ segment ℝ (lp n ε x ρ ((j:ℝ) + 1)) (lp n ε x (ρ + 1) ((j:ℝ) + 1)) →
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ≠ (n:ℝ) ^ 2 - 1 := by
    intro ρ h0 h1 e he hsub
    exact hnobΛ e he (hsub.trans ((convex_segment _ _).segment_subset
      (hrowmem ρ h0 (by linarith)) (hrowmem (ρ + 1) (by linarith) h1)))
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · subst hr0
      rw [Nat.cast_zero]
      obtain ⟨tU, hUt⟩ := hUr 0 j le_rfl (by omega)
      rw [Nat.cast_zero] at hUt
      have hdir0 : FX n ε (lp n ε x 0 ((j:ℝ) + 1) - lp n ε x (0 + 1) ((j:ℝ) + 1)) < 0 := by
        rw [map_sub, FX_lp hε, FX_lp hε]
        linarith [lv_lt (n := (n:ℝ)) (ε := ε) (x := x) hf1 (show (0:ℝ) < 0 + 1 by norm_num)]
      obtain ⟨P₀, hfP₀, hP₀, hsub₀⟩ := ext_point_of_push (GH n) hfA0
        (GH_lp (n:ℝ) ε x (0 + 1) ((j:ℝ) + 1)) hφc (hφpush _ hdir0)
      rcases C.row_step hD0 hj0
          ⟨P₀, hfP₀, hP₀, fun e _ => not_straddles_of_interior D.toDissection hsub₀ e.1 e.2⟩
          (hnobstep 0 le_rfl (by linarith)) with
        hU | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno⟩
      · exact hU
      · exact (C.row_bad0 hφπ hUt hD0 hle hθ).elim
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [Nat.cast_add, Nat.cast_one]
      obtain ⟨t₃, h3⟩ := hD (r' + 1) hr
      rw [Nat.cast_add, Nat.cast_one] at h3
      obtain ⟨t₁, h1⟩ := hD r' (by omega)
      obtain ⟨t₂, h2⟩ := hUr (r' + 1) j le_rfl (by omega)
      rw [Nat.cast_add, Nat.cast_one] at h2
      obtain ⟨t₄, h4⟩ := ih r' (by omega) (by omega)
      have hr'0 : (0:ℝ) ≤ r' := Nat.cast_nonneg r'
      have hr'q : (r':ℝ) + 1 + 1 ≤ q := by
        have h' : r' + 1 + 1 ≤ q := hr
        exact_mod_cast h'
      have hclV : ∃ P'' : Plane, GH n P'' = -((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1)) ∧
          lp n ε x ((r':ℝ) + 1) ((j:ℝ) + 1)
            ∈ openSegment ℝ P'' (lp n ε x ((r':ℝ) + 1 + 1) ((j:ℝ) + 1)) ∧
          ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1))),
            ¬ Straddles ((D.tile e.1).edge e.2) P'' (lp n ε x ((r':ℝ) + 1) ((j:ℝ) + 1))
              (lp n ε x ((r':ℝ) + 1 + 1) ((j:ℝ) + 1)) := by
        have hle4 := h4.all (P := fun p => GH n p ≤ -((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1)))
          (GH_le hf1 le_rfl) (GH_le hf1 le_rfl) (GH_le hf1 (by linarith))
        obtain ⟨k4, m4, j4, hkm4, -, -, hk4, hm4, -⟩ := h4
        have hVW : lp n ε x ((r':ℝ) + 1) ((j:ℝ) + 1) ≠ lp n ε x ((r':ℝ) + 1 + 1) ((j:ℝ) + 1) :=
          lp_ne_xi hf1 hε (by linarith)
        have hP'' : lp n ε x ((r':ℝ) + 1) ((j:ℝ) + 1)
            ∈ openSegment ℝ (lp n ε x r' ((j:ℝ) + 1)) (lp n ε x ((r':ℝ) + 1 + 1) ((j:ℝ) + 1)) := by
          refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
          unfold lp
          apply plane_ext <;>
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
        exact ⟨_, GH_lp _ _ _ _ _, hP'', clamp_b D.toDissection (GH n) (GH_ne hf1) _ hVW
          (GH_lp _ _ _ _ _) (GH_lp _ _ _ _ _) (GH_lp _ _ _ _ _) hP'' hkm4 hk4 hm4 hle4⟩
      rcases C.row_step h3 hj0 hclV (hnobstep ((r':ℝ) + 1) (by linarith) hr'q) with
        hU | ⟨ix, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle, hθ, hno⟩
      · exact hU
      · exfalso
        have hb : (r':ℝ) + 2 ≤ n := by
          have h' : r' + 2 ≤ n := by omega
          exact_mod_cast h'
        refine C.row_bad hn3 hj0 h1 h2 h3 h4 ht hm hle hθ
          (fun i hi => hno i (by rw [hi]; exact lp_congr (by ring) rfl)) hb (fun w hw => ?_)
        refine hA (r' + 1) (by omega) hr (r' + 1 + j + 1) (j + 1) (by omega) (by omega) (by omega)
          ⟨?_, ?_⟩ ?_
        · intro i' j' hj' hij'
          rcases Nat.lt_or_ge j' (j + 1) with hlt | hge
          · exact hUr i' j' (by omega) (by omega)
          · have hje : j' = j + 1 := by omega
            subst hje
            have h := ih i' (by omega) (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro i' j' hj' hij'
          rcases Nat.lt_or_ge j' j with hlt | hge
          · exact hDr i' j' hlt (by omega)
          · have hje : j' = j := by omega
            subst hje
            exact hD i' (by omega)
        · have e1 : (((r' + 1 + j + 1 : ℕ)) : ℝ) = (r':ℝ) + ((j:ℝ) + 1) + 1 := by
            push_cast; ring
          have e2 : (((j + 1 : ℕ)) : ℝ) = (j:ℝ) + 1 := by push_cast; ring
          rw [e1, e2]
          exact Or.inr ⟨w, hw⟩

end Ctx

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.Ctx.row_step
#print axioms Erdos634.Draft.SideRun.Ctx.row_bad0
#print axioms Erdos634.Draft.SideRun.Ctx.row_bad
#print axioms Erdos634.Draft.SideRun.Ctx.row
