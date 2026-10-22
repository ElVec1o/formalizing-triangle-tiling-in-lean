import Erdos634.Draft.LaczFormalWalkCorner

/-!
# A tile laid on the base is an entry of the base walk

Erdős #634, base-`β` band.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), AI assistant (item 3), Beeson–Roșu,
Beeson, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`entry_of_laid`: if a tile `i` of `D` has two vertices at the parameters `s₁ < s₂` of the base `[P, Q]`
(with the target on the left), then the walk along the base has an entry `(i, P + s₁(Q−P), P + s₂(Q−P))`.
Proof: the walk covers the base (`walk_cover`); the entry covering the midpoint shares a non-degenerate
stretch of the base with the tile's edge; two tiles on the same side of the base line cannot share two points
of their base edges (`Dissection.sameside_edges_subsingleton`), so the entry's tile is `i`, and the two
edges agree.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem seg_param {P w : Plane} (hw : w ≠ 0) {s t τ : ℝ} (hst : s ≤ t) :
    P + τ • w ∈ segment ℝ (P + s • w) (P + t • w) ↔ s ≤ τ ∧ τ ≤ t := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    have h2 : P + (a * s + b * t) • w = P + τ • w := by
      rw [← h]
      have : P = (a + b) • P := by rw [hab, one_smul]
      calc P + (a * s + b * t) • w = (a + b) • P + (a * s + b * t) • w := by rw [← this]
        _ = a • (P + s • w) + b • (P + t • w) := by module
    have h3 := smul_injective_of_ne hw (add_left_cancel h2)
    have ha' : a = 1 - b := by linarith
    subst ha'
    constructor <;> nlinarith [mul_nonneg hb (sub_nonneg.2 hst), mul_nonneg ha (sub_nonneg.2 hst)]
  · rintro ⟨h1, h2⟩
    rcases hst.lt_or_eq with hlt | heq
    · refine ⟨1 - (τ - s) / (t - s), (τ - s) / (t - s), ?_, div_nonneg (by linarith) (by linarith), by ring, ?_⟩
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · have hts : t - s ≠ 0 := by linarith
        have hq : (τ - s) / (t - s) * (t - s) = τ - s := div_mul_cancel₀ _ hts
        have : τ = (1 - (τ - s) / (t - s)) * s + (τ - s) / (t - s) * t := by
          have e : (1 - (τ - s) / (t - s)) * s + (τ - s) / (t - s) * t =
              s + (τ - s) / (t - s) * (t - s) := by ring
          rw [e, hq]; ring
        have e : (1 - (τ - s) / (t - s)) • (P + s • w) + ((τ - s) / (t - s)) • (P + t • w) =
            P + ((1 - (τ - s) / (t - s)) * s + (τ - s) / (t - s) * t) • w := by module
        rw [e, ← this]
    · have : τ = s := by linarith
      subst this; subst heq
      simp [segment_same]

theorem target_left {D : CongruentDissection N} {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) :
    ∀ y ∈ D.target.carrier, 0 ≤ cross (D.target.pts q - D.target.pts p) (y - D.target.pts p) := by
  intro y hy
  set P := D.target.pts p
  set w := D.target.pts q - P
  have hconv : Convex ℝ {y : Plane | crossL w P ≤ crossL w y} :=
    convex_halfSpace_ge (crossL w).isLinear _
  have key : ∀ y' : Plane, cross w (y' - P) = crossL w y' - crossL w P := by
    intro y'; rw [cross_sub_right]; rfl
  have hsub : Set.range D.target.pts ⊆ {y : Plane | crossL w P ≤ crossL w y} := by
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq]
    rcases fin3_cover p q r k hpq hpr hqr with h | h | h
    · rw [h]
    · have h0 := key (D.target.pts k)
      have : cross w (D.target.pts k - P) = 0 := by
        rw [h]; exact cross_self _
      linarith
    · have h0 := key (D.target.pts k)
      rw [h] at h0 ⊢
      have : 0 < cross w (D.target.pts r - P) := hori
      linarith
  have := convexHull_min hsub hconv hy
  simp only [Set.mem_setOf_eq] at this
  rw [key]; linarith

theorem edge_idx (T : Tri) (ka kb : Fin 3) (h : kb ≠ ka) :
    ∃ idx : Fin 3, T.edge idx = segment ℝ (T.pts ka) (T.pts kb) := by
  have hc : kb = ka + 1 ∨ kb = ka + 2 := by revert h; revert ka kb; decide
  rcases hc with rfl | rfl
  · exact ⟨ka, rfl⟩
  · refine ⟨ka + 2, ?_⟩
    show segment ℝ (T.pts (ka + 2)) (T.pts (ka + 2 + 1)) = _
    have : ka + 2 + 1 = ka := by revert ka; decide
    rw [this, segment_symm]

theorem crossL_on_line (w P : Plane) (s t : ℝ) {y : Plane}
    (hy : y ∈ segment ℝ (P + s • w) (P + t • w)) : crossL w y = crossL w P := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have h1 : crossL w (P + s • w) = crossL w P := by
    rw [map_add, map_smul]; simp [crossL_apply, cross_self]
  have h2 : crossL w (P + t • w) = crossL w P := by
    rw [map_add, map_smul]; simp [crossL_apply, cross_self]
  rw [map_add, map_smul, map_smul, h1, h2, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]

theorem walk_entry_tile_line {D : CongruentDissection N} {p q r : Fin 3}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {i i' : Fin N} {ke ke' : Fin 3} {s t s1 s2 : ℝ}
    (hw : D.target.pts q - D.target.pts p ≠ 0)
    (hedge : (D.tile i').edge ke = segment ℝ (D.target.pts p + s • (D.target.pts q - D.target.pts p))
      (D.target.pts p + t • (D.target.pts q - D.target.pts p)))
    (hedge' : (D.tile i).edge ke' = segment ℝ (D.target.pts p + s1 • (D.target.pts q - D.target.pts p))
      (D.target.pts p + s2 • (D.target.pts q - D.target.pts p)))
    (hne : (i', ke) ≠ (i, ke')) (a b : ℝ) (hab : a < b)
    (ha1 : s ≤ a) (ha2 : a ≤ t) (ha3 : s1 ≤ a) (ha4 : a ≤ s2)
    (hb1 : s ≤ b) (hb2 : b ≤ t) (hb3 : s1 ≤ b) (hb4 : b ≤ s2) : False := by
  set P := D.target.pts p
  set w := D.target.pts q - P
  have hf0 : (-(crossL w) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hw
    apply eq_zero_of_cross_eq_zero
    intro v
    have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g v) h
    simpa using this
  have hleft := target_left hpq hpr hqr hori
  have hle : ∀ j : Fin N, ∀ y ∈ (D.tile j).carrier, (-(crossL w)) y ≤ -(crossL w P) := by
    intro j y hy
    have := hleft y (Erdos634.BaseSelection.tile_subset_target D.toDissection j hy)
    rw [cross_sub_right] at this
    simp only [LinearMap.neg_apply, crossL_apply]
    linarith
  have hE : ∀ (u1 u2 : ℝ) (j : Fin N) (k : Fin 3), (D.tile j).edge k = segment ℝ (P + u1 • w) (P + u2 • w) →
      ∀ y ∈ (D.tile j).edge k, (-(crossL w)) y = -(crossL w P) := by
    intro u1 u2 j k he y hy
    rw [he] at hy
    simp only [LinearMap.neg_apply]
    rw [crossL_on_line w P u1 u2 hy]
  have hsub := D.sameside_edges_subsingleton (-(crossL w)) (-(crossL w P)) hf0
    (e₁ := (i', ke)) (e₂ := (i, ke')) hne (hle i') (hle i) (hE s t i' ke hedge) (hE s1 s2 i ke' hedge')
  have hpa : P + a • w ∈ (D.tile i').edge ke ∩ (D.tile i).edge ke' := by
    rw [hedge, hedge']
    exact ⟨(seg_param hw (le_trans ha1 ha2)).2 ⟨ha1, ha2⟩, (seg_param hw (le_trans ha3 ha4)).2 ⟨ha3, ha4⟩⟩
  have hpb : P + b • w ∈ (D.tile i').edge ke ∩ (D.tile i).edge ke' := by
    rw [hedge, hedge']
    exact ⟨(seg_param hw (le_trans hb1 hb2)).2 ⟨hb1, hb2⟩, (seg_param hw (le_trans hb3 hb4)).2 ⟨hb3, hb4⟩⟩
  have := hsub hpa hpb
  have := smul_injective_of_ne hw (add_left_cancel this)
  linarith

/-- **A tile laid on the base is an entry of the base walk.** -/
theorem entry_of_laid {D : CongruentDissection N} {p q r : Fin 3}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (i : Fin N) (ka kb : Fin 3) (hab : kb ≠ ka) {s1 s2 : ℝ} (h01 : 0 ≤ s1) (h12 : s1 < s2)
    (h21 : s2 ≤ 1)
    (hka : (D.tile i).pts ka = D.target.pts p + s1 • (D.target.pts q - D.target.pts p))
    (hkb : (D.tile i).pts kb = D.target.pts p + s2 • (D.target.pts q - D.target.pts p)) :
    ∃ e ∈ L, e.1 = i ∧ e.2.1 = D.target.pts p + s1 • (D.target.pts q - D.target.pts p) ∧
      e.2.2 = D.target.pts p + s2 • (D.target.pts q - D.target.pts p) := by
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  have hne : P ≠ Q := by
    intro h
    have : cross (Q - P) (D.target.pts r - P) = 0 := by rw [← h]; simp [cross]
    linarith
  have hw : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hm0 : 0 ≤ (s1 + s2) / 2 := by linarith
  have hm1 : (s1 + s2) / 2 ≤ 1 := by linarith
  obtain ⟨e, he, s, t, hsm, hmt, hst, he1, he2⟩ :=
    walk_cover hne W (t0 := 0) (t1 := 1) (by simp) (by simp) one_pos _ hm0 hm1
  obtain ⟨kk, fi, g, hk, hf, hfk, -, -, -, -⟩ := walkT_mem_step W e he
  obtain ⟨ke, hke⟩ := edge_idx (D.tile e.1) kk fi hfk
  obtain ⟨ke', hke'⟩ := edge_idx (D.tile i) ka kb hab
  rw [hk, hf, he1, he2] at hke
  rw [hka, hkb] at hke'
  have hpair : (e.1, ke) = (i, ke') := by
    by_contra hne'
    refine walk_entry_tile_line hpq hpr hqr hori hw hke hke' hne' (max s s1) (min t s2)
      (max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hst, by linarith⟩, lt_min_iff.mpr ⟨by linarith, h12⟩⟩)
      (le_max_left _ _) (max_le (le_of_lt hst) (by linarith)) (le_max_right _ _)
      (max_le (by linarith) (le_of_lt h12))
      (le_trans (le_max_left _ _) (le_of_lt (max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hst, by linarith⟩,
        lt_min_iff.mpr ⟨by linarith, h12⟩⟩))) (min_le_left _ _)
      (le_trans (le_max_right _ _) (le_of_lt (max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨hst, by linarith⟩,
        lt_min_iff.mpr ⟨by linarith, h12⟩⟩))) (min_le_right _ _)
  obtain ⟨hi, hkk⟩ := Prod.mk.inj hpair
  subst hi; subst hkk
  rw [hke] at hke'
  have hseg1 : P + s1 • (Q - P) ∈ segment ℝ (P + s • (Q - P)) (P + t • (Q - P)) := by
    rw [hke']; exact left_mem_segment _ _ _
  have hseg2 : P + s2 • (Q - P) ∈ segment ℝ (P + s • (Q - P)) (P + t • (Q - P)) := by
    rw [hke']; exact right_mem_segment _ _ _
  have hseg3 : P + s • (Q - P) ∈ segment ℝ (P + s1 • (Q - P)) (P + s2 • (Q - P)) := by
    rw [← hke']; exact left_mem_segment _ _ _
  have hseg4 : P + t • (Q - P) ∈ segment ℝ (P + s1 • (Q - P)) (P + s2 • (Q - P)) := by
    rw [← hke']; exact right_mem_segment _ _ _
  rw [seg_param hw hst.le] at hseg1 hseg2
  rw [seg_param hw h12.le] at hseg3 hseg4
  have e1 : s = s1 := le_antisymm hseg1.1 hseg3.1
  have e2 : t = s2 := le_antisymm hseg4.2 hseg2.2
  exact ⟨e, he, rfl, by rw [he1, e1], by rw [he2, e2]⟩

/-- **The token of a laid `C1` tile** (`c` on the base, `b` from the apex to the left end, `a` to the right end)
is `cAB`; **a laid `C2` tile** (`a` to the left end, `b` to the right end) is `cBA`. -/
theorem laid_tok {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (i : Fin N) (ka kb jj : Fin 3) (hkab : ka ≠ kb)
    (hkaj : ka ≠ jj) (hkbj : kb ≠ jj) {V1 V2 : Plane} (hV1 : (D.tile i).pts ka = V1)
    (hV2 : (D.tile i).pts kb = V2) (hlen : dist V1 V2 = sideOpp D.model 2) :
    ((dist ((D.tile i).pts kb) ((D.tile i).pts jj) = sideOpp D.model 0) →
      elemTok D α β (i, V1, V2) = Tok.cAB) ∧
    ((dist ((D.tile i).pts kb) ((D.tile i).pts jj) = sideOpp D.model 1) →
      elemTok D α β (i, V1, V2) = Tok.cBA) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  have hang := angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i ka kb jj hkab hkaj hkbj
  have hxA : dist V1 V2 ≠ sideOpp D.model 0 := by rw [hlen]; exact hac.symm
  have hxB : dist V1 V2 ≠ sideOpp D.model 1 := by rw [hlen]; exact hbc.symm
  have hsd : sideOfLen (sideOpp D.model 0) (sideOpp D.model 1) (dist V1 V2) = .c :=
    sideOfLen_c hxA hxB
  constructor
  · intro h
    have hA := hang.1 h
    rw [hV1] at hA
    unfold elemTok
    simp only []
    rw [hsd, cornerOfAng_A hA]; rfl
  · intro h
    have hB := hang.2.1 h
    rw [hV1] at hB
    unfold elemTok
    simp only []
    rw [hsd, cornerOfAng_B (by rw [hB]; exact hαβ.symm) hB]; rfl

#print axioms entry_of_laid
#print axioms laid_tok

end Erdos634.LaczJunction.Walk
