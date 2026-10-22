/-
Draft/SideRunChord.lean -- Stage 2b of the formalization of the side theorem of room GAP3: the standing hypotheses of
the run lemma and its local lemmas ((private working notes, not included), sections 1-2).

* `Ctx D n α β γ L ax ay ε x`: a `Setup`, an orientation `ε = ±1`, and hypothesis (K1) at `P = (x, 0)` in the form
  `hK1`: no tile of the side `σ` has both `P` and `p(0,1)` as vertices (`hch`: the chords from `P` are interior);
* `Ctx.seg_int`: a segment between two lattice points of the target is interior to the target as soon as one end is
  above the side, one end has a point of the target ahead on its row, one end has one behind;
* `RhoEdge`, `K3`: hypothesis (K3) (the side `ρ_s` of the line `m_s` is outside the target, or one tile of that side
  has an edge on `m_s` from height `≤ j0` to height `> s`); `Ctx.K3_clamp`: the clamp it gives;
* `Ctx.m_next`: the tile across the `a`-edge of `U(ξ,η)` at `p(ξ+1,η)` is `D(ξ,η)`, or `N(ξ,η)`, or it lays more
  than `a` and gives (K3) for a shorter run; `Ctx.m_clamp_base`, `Ctx.m_clamp_tile`: the clamps it needs;
* `Ctx.chord`: the chord principle; `Ctx.phi`: the tile `φ_{j−1}` at `p(0,j)`;
* `N_push`: the points `p(ξ+δ, η+1)`, `0 < δ ≤ 1/3`, are interior to `N(ξ,η)`.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunLattice
import Erdos634.Draft.SideRunWords

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.W2E1 Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay ε x : ℝ}

theorem lp_one (n ε x ξ η : ℝ) : (lp n ε x ξ η) 1 = η * hh n := by
  unfold lp; rw [mkPt_one]

theorem nu_lt_one {n : ℝ} (hn : 1 < n) : nu n < 1 := by
  have h : (0:ℝ) < n ^ 2 := by nlinarith
  unfold nu
  rw [div_lt_one h]
  linarith

/-! ## 1. Interior segments -/

namespace Setup

theorem fwd1 (S : Setup D n α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lp n 1 x (ξ + δ) η ∈ D.target.carrier) : 0 < gB L ax ay (lp n 1 x ξ η) := by
  have e : lp (n:ℝ) 1 x (ξ + δ) η
      = mkPt (x + 1 * ((ξ + η) * (n:ℝ) ^ 2 - η * uu n) + δ * (n:ℝ) ^ 2) (η * hh n) := by
    unfold lp; exact mkPt_congr (by ring) rfl
  rw [e] at h
  exact S.gB_pos_of_right (mul_pos hδ S.c_pos) h

theorem bwd1 (S : Setup D n α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lp n 1 x (ξ - δ) η ∈ D.target.carrier) : 0 < gA ax ay (lp n 1 x ξ η) := by
  have e : lp (n:ℝ) 1 x (ξ - δ) η
      = mkPt (x + 1 * ((ξ + η) * (n:ℝ) ^ 2 - η * uu n) - δ * (n:ℝ) ^ 2) (η * hh n) := by
    unfold lp; exact mkPt_congr (by ring) rfl
  rw [e] at h
  exact S.gA_pos_of_left (mul_pos hδ S.c_pos) h

theorem fwdm (S : Setup D n α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lp n (-1) x (ξ + δ) η ∈ D.target.carrier) : 0 < gA ax ay (lp n (-1) x ξ η) := by
  have e : lp (n:ℝ) (-1) x (ξ + δ) η
      = mkPt (x + (-1) * ((ξ + η) * (n:ℝ) ^ 2 - η * uu n) - δ * (n:ℝ) ^ 2) (η * hh n) := by
    unfold lp; exact mkPt_congr (by ring) rfl
  rw [e] at h
  exact S.gA_pos_of_left (mul_pos hδ S.c_pos) h

theorem bwdm (S : Setup D n α β γ L ax ay) {ξ η δ : ℝ} (hδ : 0 < δ)
    (h : lp n (-1) x (ξ - δ) η ∈ D.target.carrier) : 0 < gB L ax ay (lp n (-1) x ξ η) := by
  have e : lp (n:ℝ) (-1) x (ξ - δ) η
      = mkPt (x + (-1) * ((ξ + η) * (n:ℝ) ^ 2 - η * uu n) + δ * (n:ℝ) ^ 2) (η * hh n) := by
    unfold lp; exact mkPt_congr (by ring) rfl
  rw [e] at h
  exact S.gB_pos_of_right (mul_pos hδ S.c_pos) h

end Setup

/-- **The standing hypotheses of the run lemma**: a `Setup`, an orientation, and (K1) at `P = (x, 0)`. -/
structure Ctx (D : CongruentDissection N) (n : ℕ) (α β γ L ax ay ε x : ℝ) : Prop where
  S : Setup D n α β γ L ax ay
  hε : ε = 1 ∨ ε = -1
  hK1 : ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n ε x 0 0 →
    (D.tile t').pts m = lp n ε x 0 1 → (∀ i, FX n ε ((D.tile t').pts i) ≤ lv n ε x 0) → False
  hch : ∀ j : ℕ, 1 ≤ j → lp n ε x 0 j ∈ D.target.carrier →
    openSegment ℝ (lp n ε x 0 0) (lp n ε x 0 j) ⊆ interior D.target.carrier

namespace Ctx

theorem e2 (C : Ctx D n α β γ L ax ay ε x) : ε ^ 2 = 1 := by
  rcases C.hε with h | h <;> rw [h] <;> norm_num

/-- **Interior segments between lattice points.** -/
theorem seg_int (C : Ctx D n α β γ L ax ay ε x) {ξ η ξ' η' : ℝ}
    (hA : lp n ε x ξ η ∈ D.target.carrier) (hB : lp n ε x ξ' η' ∈ D.target.carrier)
    (hh' : 0 < η ∨ 0 < η')
    (hF : (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ + δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ' + δ) η' ∈ D.target.carrier))
    (hBk : (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ - δ) η ∈ D.target.carrier) ∨
      (∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ' - δ) η' ∈ D.target.carrier)) :
    openSegment ℝ (lp n ε x ξ η) (lp n ε x ξ' η') ⊆ interior D.target.carrier := by
  have hhp := hh_pos C.S.f1
  have h1 : 0 < (lp n ε x ξ η) 1 ∨ 0 < (lp n ε x ξ' η') 1 := by
    rcases hh' with h | h
    · left; rw [lp_one]; exact mul_pos h hhp
    · right; rw [lp_one]; exact mul_pos h hhp
  have S := C.S
  rcases C.hε with rfl | rfl
  · refine S.interior_seg hA hB h1 ?_ ?_
    · rcases hBk with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.bwd1 hδ h)
      · exact Or.inr (S.bwd1 hδ h)
    · rcases hF with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.fwd1 hδ h)
      · exact Or.inr (S.fwd1 hδ h)
  · refine S.interior_seg hA hB h1 ?_ ?_
    · rcases hF with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.fwdm hδ h)
      · exact Or.inr (S.fwdm hδ h)
    · rcases hBk with ⟨δ, hδ, h⟩ | ⟨δ, hδ, h⟩
      · exact Or.inl (S.bwdm hδ h)
      · exact Or.inr (S.bwdm hδ h)

end Ctx

/-! ## 2. Hypothesis (K3) -/

/-- tile `w` lies on the side `ρ_s` of the line `m_s` and has an edge on it from height `η₁ ≤ j0` to height
`η₂ > s` -/
def RhoEdge (D : CongruentDissection N) (n ε x : ℝ) (w : Fin N) (s j0 : ℝ) : Prop :=
  ∃ (k m : Fin 3) (η₁ η₂ : ℝ), k ≠ m ∧ (D.tile w).pts k = lp n ε x (s - η₁) η₁ ∧
    (D.tile w).pts m = lp n ε x (s - η₂) η₂ ∧ η₁ ≤ j0 ∧ s < η₂ ∧
    ∀ i, GS n ε ((D.tile w).pts i) ≤ -lv n ε x s

/-- **Hypothesis (K3)**: the side `ρ_s` is outside the target, or one tile of that side has an edge on `m_s` that
contains the points `p(s−j, j)`, `j0 < j ≤ s`, in its relative interior. -/
def K3 (D : CongruentDissection N) (n ε x : ℝ) (s j0 : ℝ) : Prop :=
  (∀ q ∈ D.target.carrier, -lv n ε x s ≤ GS n ε q) ∨ ∃ w, RhoEdge D n ε x w s j0

theorem K3.mono {n' s j0 j0' : ℝ} (h : K3 D n' ε x s j0) (hj : j0 ≤ j0') : K3 D n' ε x s j0' := by
  rcases h with h | ⟨w, k, m, η₁, η₂, hkm, hk, hm, h1, h2, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, k, m, η₁, η₂, hkm, hk, hm, le_trans h1 hj, h2, hle⟩

namespace Ctx

/-- **The clamp given by (K3)** at the point `p(s−η, η)`, `j0 < η ≤ s`, for a wall `[p, Q]` on a line `{F = c}`
that reaches `p` from the side away from `ρ_s`. -/
theorem K3_clamp (C : Ctx D n α β γ L ax ay ε x) {s j0 η : ℝ} (hK : K3 D n ε x s j0)
    (h1 : j0 < η) (h2 : η ≤ s) (F : Plane →ₗ[ℝ] ℝ) (c : ℝ) {Q : Plane}
    (hFp : F (lp n ε x (s - η) η) = c) (hFQ : F Q = c)
    (hdir : GS n ε (lp n ε x (s - η) η - Q) < 0) :
    ∃ Q' : Plane, F Q' = c ∧ lp n ε x (s - η) η ∈ openSegment ℝ Q' Q ∧
      ∀ e ∈ D.lineChain F c, ¬ Straddles ((D.tile e.1).edge e.2) Q' (lp n ε x (s - η) η) Q := by
  have hε := C.e2
  have hGp : GS n ε (lp n ε x (s - η) η) = -lv n ε x s := by
    rw [GS_lp hε]; unfold lv; ring
  rcases hK with hout | ⟨w, k, m, η₁, η₂, hkm, hk, hm, hη₁, hη₂, hle⟩
  · refine ⟨lp n ε x (s - η) η + (1:ℝ) • (lp n ε x (s - η) η - Q), ext_level F hFp hFQ 1,
      mem_openSegment_ext _ Q one_pos, ?_⟩
    refine clamp_out D.toDissection F c (fun r hr hmem => ?_)
    have h3 := hout _ hmem
    rw [map_add, map_smul, smul_eq_mul, hGp] at h3
    nlinarith [mul_pos hr (neg_pos.mpr hdir)]
  · have hd : 0 < η₂ - η₁ := by linarith
    have hx : lp n ε x (s - η) η ∈ openSegment ℝ ((D.tile w).pts k) ((D.tile w).pts m) := by
      rw [hk, hm]
      have hab : (η₂ - η) / (η₂ - η₁) + (η - η₁) / (η₂ - η₁) = 1 := by
        rw [← add_div, show η₂ - η + (η - η₁) = η₂ - η₁ by ring]
        exact div_self hd.ne'
      have hb : (η - η₁) / (η₂ - η₁) * (η₂ - η₁) = η - η₁ := div_mul_cancel₀ _ hd.ne'
      have hη : (η₂ - η) / (η₂ - η₁) * η₁ + (η - η₁) / (η₂ - η₁) * η₂ = η := by
        linear_combination hb + η₁ * hab
      refine ⟨(η₂ - η) / (η₂ - η₁), (η - η₁) / (η₂ - η₁), div_pos (by linarith) hd,
        div_pos (by linarith) hd, hab, ?_⟩
      unfold lp
      apply plane_ext
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero]
        linear_combination (x + ε * s * (n:ℝ) ^ 2) * hab - (ε * uu n) * hη
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_one]
        linear_combination (hh n) * hη
    obtain ⟨hpw, -, hpush⟩ := edge_interior_push (D.tile w) hkm (GS n ε) (GS_ne C.S.f1 hε)
      (-lv n ε x s) (by rw [hk, GS_lp hε]; unfold lv; ring) (by rw [hm, GS_lp hε]; unfold lv; ring)
      hle hx
    obtain ⟨Q', h1', h2', h3'⟩ := ext_point_of_push F hFp hFQ hpw (hpush _ hdir)
    exact ⟨Q', h1', h2', fun e _ => not_straddles_of_interior D.toDissection h3' e.1 e.2⟩

/-- the tile found across an `a`-edge lays exactly `a`, or it gives (K3) for the run that ends there -/
theorem m_next_cases (C : Ctx D n α β γ L ax ay ε x) {i : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    {ξ η t : ℝ} (hk : (D.tile i).pts k = lp n ε x (ξ + 1) η) (ht : 0 < t)
    (hm : (D.tile i).pts m = AffineMap.lineMap (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) t)
    (hle : ∀ j, GS n ε ((D.tile i).pts j) ≤ -lv n ε x (ξ + η + 1)) (hb : ξ + 2 ≤ n) :
    (D.tile i).pts m = lp n ε x ξ (η + 1) ∨ RhoEdge D n ε x i (ξ + η + 1) η := by
  have hε := C.e2
  have hf1 := C.S.f1
  have hf0 := C.S.f0
  rw [lineMap_lp] at hm
  have hd : dist ((D.tile i).pts k) ((D.tile i).pts m) = t * n := by
    rw [hk, hm]
    exact dist_lp hf1 hε (by positivity) (by unfold Qf; ring)
  have hk' : (D.tile i).pts k = lp n ε x (ξ + η + 1 - η) η := by
    rw [hk]; exact lp_congr (by ring) rfl
  have hm' : (D.tile i).pts m = lp n ε x (ξ + η + 1 - (η + t)) (η + t) := by
    rw [hm]; exact lp_congr (by ring) (by ring)
  have hstep : (ξ + 1) * (n:ℝ) ≤ ((n:ℝ) - 1) * n :=
    mul_le_mul_of_nonneg_right (by linarith) hf0.le
  have hlong : (n:ℝ) ^ 2 - 1 ≤ t * n → ξ + η + 1 < η + t := by
    intro h
    by_contra hc
    push Not at hc
    have h3 := mul_le_mul_of_nonneg_right (show t ≤ ξ + 1 by linarith) hf0.le
    nlinarith
  rcases vertex_dist_cases D C.S.hM i hkm with h | h | h
  · left
    have h1 : t * (n:ℝ) = 1 * n := by rw [one_mul, ← hd, h]
    have ht1 : t = 1 := mul_right_cancel₀ hf0.ne' h1
    rw [hm, ht1]
    exact lp_congr (by ring) (by ring)
  · right
    exact ⟨k, m, η, η + t, hkm, hk', hm', le_refl _, hlong (le_of_eq (by rw [← hd, h])), hle⟩
  · right
    exact ⟨k, m, η, η + t, hkm, hk', hm', le_refl _, hlong (by rw [← hd, h]; linarith), hle⟩

/-- **The tile across the `a`-edge of `U(ξ,η)` at `p(ξ+1,η)`**: it is `D(ξ,η)`, or `N(ξ,η)`, or it lays more than
`a` on the line `m_{ξ+η+1}` and gives (K3) for the run of length `ξ+η+1` at height `η`. -/
theorem m_next (C : Ctx D n α β γ L ax ay ε x) {ξ η : ℝ} {t₀ : Fin N}
    (hU : HasV D t₀ (lp n ε x ξ η) (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1))) (hη : 0 ≤ η)
    (hFw : ∃ δ : ℝ, 0 < δ ∧ lp n ε x (ξ + 1 + δ) η ∈ D.target.carrier)
    (hcl : ∃ P' : Plane, GS n ε P' = -lv n ε x (ξ + η + 1) ∧
      lp n ε x (ξ + 1) η ∈ openSegment ℝ P' (lp n ε x ξ (η + 1)) ∧
      ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x (ξ + η + 1)),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)))
    (hb : ξ + 2 ≤ n) :
    (∃ t, HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ + 1) (η + 1))) ∨
    (∃ t, HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n))) ∨
    (∃ w, RhoEdge D n ε x w (ξ + η + 1) η) := by
  have hε := C.e2
  have hf1 := C.S.f1
  have hVG : lp n ε x (ξ + 1) η ≠ lp n ε x ξ (η + 1) := lp_ne_eta hf1 (by linarith)
  have hfV : GS n ε (lp n ε x (ξ + 1) η) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hfG : GS n ε (lp n ε x ξ (η + 1)) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hint : openSegment ℝ (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1))
      ⊆ interior D.target.carrier := by
    refine C.seg_int hU.mem₂ hU.mem₃ (Or.inr (by linarith)) (Or.inl hFw) (Or.inl ⟨1, one_pos, ?_⟩)
    rw [show ξ + 1 - 1 = ξ by ring]; exact hU.mem₁
  have hwall : ∀ y ∈ openSegment ℝ (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hU
    refine seg_wall D.toDissection (t := t₀) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨P', hfP', hP', hP⟩ := hcl
  obtain ⟨e, he, k', m', t, hk'm', hk', ht, hm', hle, -, -⟩ :=
    next_tile D.toDissection (GS n ε) (GS_ne hf1 hε) (-lv n ε x (ξ + η + 1)) hVG hfV hfG hfP' hP'
      hint hwall hP
  rcases C.m_next_cases hk'm' hk' ht hm' hle hb with hG | hR
  · rcases m_edge_cases C.S hε hk'm' hk' hG hle with h | h
    · exact Or.inl ⟨e.1, h⟩
    · exact Or.inr (Or.inl ⟨e.1, h⟩)
  · exact Or.inr (Or.inr ⟨e.1, hR⟩)

/-- the clamp of an `a`-edge at a point of the side: the line leaves the target below the side -/
theorem m_clamp_base (C : Ctx D n α β γ L ax ay ε x) (ξ : ℝ) :
    ∃ P' : Plane, GS n ε P' = -lv n ε x (ξ + 0 + 1) ∧
      lp n ε x (ξ + 1) 0 ∈ openSegment ℝ P' (lp n ε x ξ (0 + 1)) ∧
      ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x (ξ + 0 + 1)),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x (ξ + 1) 0) (lp n ε x ξ (0 + 1)) := by
  have hε := C.e2
  have hfV : GS n ε (lp n ε x (ξ + 1) 0) = -lv n ε x (ξ + 0 + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hfG : GS n ε (lp n ε x ξ (0 + 1)) = -lv n ε x (ξ + 0 + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  refine ⟨lp n ε x (ξ + 1) 0 + (1:ℝ) • (lp n ε x (ξ + 1) 0 - lp n ε x ξ (0 + 1)),
    ext_level (GS n ε) hfV hfG 1, mem_openSegment_ext _ _ one_pos,
    clamp_out D.toDissection _ _ (C.S.below_out ?_ ?_)⟩
  · rw [lp_one]; ring
  · rw [lp_one]
    have := hh_pos C.S.f1
    linarith

/-- the clamp of an `a`-edge at `p(ξ+1,η)` by a tile of the side `ρ` with the edge `[p(ξ+2,η−1), p(ξ+1,η)]` -/
theorem m_clamp_tile (C : Ctx D n α β γ L ax ay ε x) {ξ η : ℝ} {t₁ : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile t₁).pts k = lp n ε x (ξ + 2) (η - 1))
    (hm : (D.tile t₁).pts m = lp n ε x (ξ + 1) η)
    (hle : ∀ i, GS n ε ((D.tile t₁).pts i) ≤ -lv n ε x (ξ + η + 1)) :
    ∃ P' : Plane, GS n ε P' = -lv n ε x (ξ + η + 1) ∧
      lp n ε x (ξ + 1) η ∈ openSegment ℝ P' (lp n ε x ξ (η + 1)) ∧
      ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x (ξ + η + 1)),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) := by
  have hε := C.e2
  have hf1 := C.S.f1
  have hVG : lp n ε x (ξ + 1) η ≠ lp n ε x ξ (η + 1) := lp_ne_eta hf1 (by linarith)
  have hfV : GS n ε (lp n ε x (ξ + 1) η) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hfG : GS n ε (lp n ε x ξ (η + 1)) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hfP' : GS n ε (lp n ε x (ξ + 2) (η - 1)) = -lv n ε x (ξ + η + 1) := by
    rw [GS_lp hε]; unfold lv; ring
  have hP' : lp n ε x (ξ + 1) η ∈ openSegment ℝ (lp n ε x (ξ + 2) (η - 1)) (lp n ε x ξ (η + 1)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    unfold lp
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  exact ⟨_, hfP', hP', clamp_b D.toDissection (GS n ε) (GS_ne hf1 hε) _ hVG hfV hfG hfP' hP' hkm hk
    hm hle⟩

/-! ## 3. The chord principle -/

/-- **The chord principle.**  If `U(0,j')` is a tile for `j' < j`, `1 ≤ j < n`, the end `p(0,j)` of the chord
`[P, p(0,j)]` is straddled by an edge of a tile of the side `σ`. -/
theorem chord (C : Ctx D n α β γ L ax ay ε x) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (hU : ∀ j' : ℕ, j' < j → UT D n ε x 0 j') {Q' : Plane} (hfQ' : FX n ε Q' = lv n ε x 0)
    (hQ' : lp n ε x 0 j ∈ openSegment ℝ (lp n ε x 0 0) Q')
    (hclamp : ∀ e ∈ D.lineChain (FX n ε) (lv n ε x 0),
      ¬ Straddles ((D.tile e.1).edge e.2) Q' (lp n ε x 0 j) (lp n ε x 0 0)) : False := by
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  have hf0 := S.f0
  have hb := S.b_pos
  have hhp := hh_pos hf1
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
  have hPE : lp n ε x 0 0 ≠ lp n ε x 0 j := lp_ne_eta hf1 hjpos.ne
  have hfP : FX n ε (lp n ε x 0 0) = lv n ε x 0 := FX_lp hε 0 0
  have hfE : FX n ε (lp n ε x 0 j) = lv n ε x 0 := FX_lp hε 0 j
  have hEmem : lp n ε x 0 j ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hU (j - 1) (by omega)
    have hc : ((j - 1 : ℕ) : ℝ) + 1 = j := by
      rw [Nat.cast_sub hj1, Nat.cast_one]; ring
    have := ht.mem₃
    rwa [hc] at this
  have hint := C.hch j hj1 hEmem
  have hwall : ∀ y ∈ openSegment ℝ (lp n ε x 0 0) (lp n ε x 0 j),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ segment ℝ (lp n ε x 0 0) (lp n ε x (0 + j * 0) (0 + j * 1)) := by
      rw [show lp n ε x (0 + (j:ℝ) * 0) (0 + (j:ℝ) * 1) = lp n ε x 0 j from
        lp_congr (by ring) (by ring)]
      exact openSegment_subset_segment ℝ _ _ hy
    obtain ⟨i', hi', hyi⟩ := seg_split_lp hj1 hy'
    obtain ⟨t, k, m, j₃, hkm, hkj, hmj, hk, hm, hj⟩ := hU i' hi'
    refine seg_wall D.toDissection (t := t) hkj ?_
    rw [hk, hj]
    rw [show lp n ε x (0 + (i':ℝ) * 0) (0 + (i':ℝ) * 1) = lp n ε x 0 i' from
      lp_congr (by ring) (by ring),
      show lp n ε x (0 + ((i':ℝ) + 1) * 0) (0 + ((i':ℝ) + 1) * 1) = lp n ε x 0 ((i':ℝ) + 1) from
      lp_congr (by ring) (by ring)] at hyi
    exact hyi
  have hP1 : (lp n ε x 0 0) 1 = 0 := by rw [lp_one]; ring
  have hE1 : 0 < (lp n ε x 0 j) 1 := by rw [lp_one]; exact mul_pos hjpos hhp
  obtain ⟨iT, kT, mT, x4, y4, z4, hkmT, hkT, hmT, hleT, hsumT⟩ :=
    wall_first D S.hM (FX n ε) (FX_ne hf1 hε) (lv n ε x 0) hPE hfP hfE (ext_level _ hfP hfE 1) hfQ'
      (mem_openSegment_ext _ _ one_pos) hQ' hint hwall
      (clamp_out D.toDissection _ _ (S.below_out hP1 hE1)) hclamp
  have hdPE : dist (lp n ε x 0 0) (lp n ε x 0 j) = (j:ℝ) * ((n:ℝ) ^ 2 - 1) :=
    dist_lp hf1 hε (mul_nonneg hjpos.le hb.le) (by unfold Qf; ring)
  rw [hdPE] at hsumT
  have hℓ := vertex_dist_cases D S.hM iT hkmT
  rw [hkT] at hℓ
  have hlen := first_len_jb S.hn2 hjn hℓ hsumT
  have h01 : lp n ε x 0 1 ∈ segment ℝ (lp n ε x 0 0) (lp n ε x 0 j) := by
    have h := lp_mem_seg (n := n) (ε := ε) (x := x) (ξ := 0) (η := 0) (ξ' := 0) (η' := j)
      (τ := 1 / j) (by positivity) (by rw [div_le_one hjpos]; exact_mod_cast hj1)
    rw [show lp n ε x (0 + 1 / (j:ℝ) * (0 - 0)) (0 + 1 / (j:ℝ) * ((j:ℝ) - 0)) = lp n ε x 0 1 from
      lp_congr (by ring) (by rw [sub_zero, one_div, inv_mul_cancel₀ hjpos.ne', zero_add])] at h
    exact h
  have hd01 : dist (lp n ε x 0 0) (lp n ε x 0 1) = (n:ℝ) ^ 2 - 1 := by
    have := dist_step_v (x := x) hf1 hε 0 0
    rwa [zero_add] at this
  have hmTeq : (D.tile iT).pts mT = lp n ε x 0 1 :=
    eq_of_mem_segment_of_dist hPE hmT h01 (by rw [hlen, hd01])
  exact C.hK1 iT kT mT hkmT hkT hmTeq hleT

/-- **The tile `φ_{j−1}`** at the end `p(0,j)` of the chord: it shows a straight angle there and contains every
short push from `p(0,j)` to the side `σ`. -/
theorem phi (C : Ctx D n α β γ L ax ay ε x) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (hU : ∀ j' : ℕ, j' < j → UT D n ε x 0 j') :
    ∃ φ : Fin N, lp n ε x 0 j ∈ (D.tile φ).carrier ∧
      (D.tile φ).localAngle (lp n ε x 0 j) = Real.pi ∧
      ∀ w : Plane, FX n ε w < 0 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
        lp n ε x 0 j + ε' • w ∈ interior (D.tile φ).carrier := by
  have hε := C.e2
  have hf1 := C.S.f1
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
  have hEP : lp n ε x 0 j ≠ lp n ε x 0 0 := lp_ne_eta hf1 hjpos.ne'
  have hfP : FX n ε (lp n ε x 0 0) = lv n ε x 0 := FX_lp hε 0 0
  have hfE : FX n ε (lp n ε x 0 j) = lv n ε x 0 := FX_lp hε 0 j
  have hQ' := mem_openSegment_ext (lp n ε x 0 j) (lp n ε x 0 0) one_pos
  by_contra hno
  refine C.chord hj1 hjn hU (ext_level (FX n ε) hfE hfP 1) (by rw [openSegment_symm]; exact hQ')
    (fun e he hs => hno ?_)
  obtain ⟨h1, h2, h3⟩ := straddle_data D.toDissection (FX n ε) (FX_ne hf1 hε) (lv n ε x 0) hEP hfE
    hfP (ext_level (FX n ε) hfE hfP 1) hQ' he hs
  exact ⟨e.1, h1, h2, h3⟩

end Ctx

/-! ## 4. The mirror tile `N(ξ,η)` -/

/-- **The points `p(ξ+δ, η+1)`, `0 < δ ≤ 1/3`, are interior to `N(ξ,η)`.** -/
theorem N_push (S : Setup D n α β γ L ax ay) {t : Fin N} {ξ η δ : ℝ}
    (h : HasV D t (lp n ε x (ξ + 1) η) (lp n ε x ξ (η + 1)) (lp n ε x (ξ - nu n) (η + 2 + nu n)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) : lp n ε x (ξ + δ) (η + 1) ∈ interior (D.tile t).carrier := by
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h
  have hν0 := nu_pos S.f1
  have hν1 := nu_lt_one S.f1
  have e : lp n ε x (ξ + δ) (η + 1)
      = (δ * (1 + nu n)) • (D.tile t).pts k + (1 - δ * (2 + nu n)) • (D.tile t).pts m
        + δ • (D.tile t).pts j := by
    rw [hk, hm, hj]
    unfold lp
    apply plane_ext <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mkPt_zero, mkPt_one] <;> ring
  rw [e]
  exact abc_interior (D.tile t) hkm hkj hmj (mul_pos hδ0 (by linarith))
    (by nlinarith [mul_le_mul_of_nonneg_right hδ1 (show (0:ℝ) ≤ 2 + nu n by linarith)]) hδ0 (by ring)

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.Ctx.seg_int
#print axioms Erdos634.Draft.SideRun.Ctx.K3_clamp
#print axioms Erdos634.Draft.SideRun.Ctx.m_next
#print axioms Erdos634.Draft.SideRun.Ctx.chord
#print axioms Erdos634.Draft.SideRun.Ctx.phi
#print axioms Erdos634.Draft.SideRun.N_push
