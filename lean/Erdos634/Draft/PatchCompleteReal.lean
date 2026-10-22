-- Draft/PatchCompleteReal.lean — S4(k) (patch completeness in the L_c phase, BY COMPOSITION, with
-- the repaired kill order of review2_R8S4), R9 (Π(k) → Π(k+1) after L_c) and S5 + S5-M (the pure-chain
-- end), for REAL `m = 1` dissections in the apex frame.  Statements of record:
-- (private working notes, not included) §§5.11, 5.12, 5.13, the appended review record ("S4 ORDERING
-- REPAIR", review2_R8S4; review2_S5).  Imported into All.lean (Erdos634/All.lean:430).
--
-- Build (scratch oleans; never .lake): RowLineP2Real olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/PatchCompleteReal.lean'
--
-- Composition (every link cited, none re-derived):
--   R8(k)      `r8_ad`, `r8_row`, `r8_corner` (Draft/LemmaGADReal, LemmaGRowReal, LemmaGCornerReal)
--   PK·a(k)    `pka_frame` (Draft/MirrorLevelQReal)          — kills `N_k` (AD mirrors, fill (N_k, Z₀))
--   P2(k)      `p2_frame` (Draft/RowLineP2Real)              — kills `G_k`, `σ_b`, the Λ₂ slot swaps
--   RW(i)      `rw_frame` (Draft/RowWallInduction)           — kills `σ_3` (C(k,k)), the Λ₃ slot swaps
--   slots      `slot2` (Λ₂), `slot_int` (Λ₃), `slot_leg` (leg; lem:sidenob, **m = 1**)
--   chain end  `chain_alpha` (R4 Step 2, Lemma A, **m = 1**)
-- Kill ORDER (review2_R8S4 repair), as executed below: (1) every `AD_k` far tile is the half-turn
-- (a mirror forces `N_k`, PK·a(k)) — this already supplies P2(k)'s hypothesis (P2-b), the level-`k`
-- down cells; (2) `G_k` and the row-`k` mirrors (P2(k)), so every row-`k` far tile is the half-turn;
-- (3) the corner `kP′` (six fills, `r8_corner`: `N_k` by PK·a, `G_k` and `σ_b` by P2(k), `σ_3` by
-- RW(k) with C(k,k), whose (i) needs the row-`k` half-turns of step (2)); (4) the interior slots
-- (P2(k−i), RW(i)); (5) the leg slot `J_k` (lem:sidenob).  `kV` is left free.
import Erdos634.Draft.RowLineP2Real

namespace Erdos634.Draft.RowWallReal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.HalfTurnR3R4
open Erdos634.Draft.HalfTurnR3R4Glue Erdos634.Draft.CornerAdjacency
open Erdos634.Draft.HalfTurnR3R4Order Erdos634.Draft.MirrorStripR2Real
open Erdos634.Draft.HalfTurnR4Real

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ}
variable (F : HFrame D e f α β γ)

/-! ## §1 The mirrors `N_k`, `G_k` identified -/

theorem dist_Lam_eq {x y x' y' p q : ℝ} (h1 : x - x' = p) (h2 : y - y' = q) :
    dist (Lam F x y) (Lam F x' y') = ‖vec F p q‖ := by
  rw [dist_Lam, h1, h2]

/-- **A mirror is the other point at the same two distances** (planar: at most two such points,
`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`). -/
theorem mirror_ident {X Y Z M C : Plane} (hYZ : Y ≠ Z) (hXC : X ≠ C) (hM : IsMirror X Y Z M)
    (hCY : dist C Y = dist X Y) (hCZ : dist C Z = dist X Z) : M = C := by
  obtain ⟨hMX, hMY, hMZ⟩ := hM
  have hd2 : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd2 hYZ hXC rfl hCY hMY rfl
      hCZ hMZ with h | h
  · exact absurd h hMX
  · exact h

/-- **The `AD_k` mirror at `kP′` is `N_k`**: the mirror of `T₂ + (k−1)P′` across its `a`-edge is
`N_k = M₁ + (k−1)P′`, third vertex `kP′ + b·uL`. -/
theorem mirT2_Nq (FC : ApexPlacement.FrameCoords F) (K' : ℕ) (h : MirT2 F (K' + 1) 0) :
    Present D (Nq F (K' + 1)) := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hbr0, -, -⟩ := bcr_facts F
  obtain ⟨hcb0, -⟩ := cb_pos F
  obtain ⟨M, hM, hP⟩ := h
  simp only [Nat.cast_zero, zero_mul, add_zero, neg_zero, zero_add, one_mul] at hM hP
  push_cast at hM hP
  have hMe : M = Lam F ((K' : ℝ) + 1) (bcr e f) := by
    refine mirror_ident (Lam_ne F FC (Or.inr (by norm_num)))
      (Lam_ne F FC (Or.inr (by intro h; linarith))) hM ?_ ?_
    · have l1 : dist (Lam F ((K' : ℝ) + 1) (bcr e f)) (Lam F ((K' : ℝ) + 1 + cb e f) (-1))
          = (f : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := -(cb e f)) (q := bcr e f + 1) (by ring) (by ring)]
        apply norm_of_sq hc0.le _ (norm_nonneg _)
        rw [norm_vec_sq, bcr, cb]
        have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
        field_simp; ring
      have r1 : dist (Lam F ((K' : ℝ) + 1 - 1) 0) (Lam F ((K' : ℝ) + 1 + cb e f) (-1))
          = (f : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := -(1 + cb e f)) (q := 1) (by ring) (by ring),
          show vec F (-(1 + cb e f)) 1 = - vec F (1 + cb e f) (-1) by rw [vec_neg]; norm_num,
          norm_neg, norm_V]
      rw [l1, r1]
    · have l1 : dist (Lam F ((K' : ℝ) + 1) (bcr e f)) (Lam F ((K' : ℝ) + 1) 0)
          = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := 0) (q := bcr e f) (by ring) (by ring), norm_vec_0q F hbr0.le, bcr,
          div_mul_cancel₀ _ hc0.ne']
      have r1 : dist (Lam F ((K' : ℝ) + 1 - 1) 0) (Lam F ((K' : ℝ) + 1) 0)
          = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := -1) (q := 0) (by ring) (by ring), norm_vec_m10]
      rw [l1, r1]
  rw [hMe] at hP
  rw [Nq_eq F FC]; push_cast
  rw [show ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 = bcr e f from rfl]
  exact hP

/-- **The row-`k` mirror at `kP′` is `G_k`, and it lays `b` on `ℓ_k`'s band side from `kP′`**: the
mirror of `T₃ + (k−1)P′` across its `a`-edge has third vertex `kP′ + b·u_r = Q2 (b/c) k`. -/
theorem mirUp_seed (FC : ApexPlacement.FrameCoords F) (K' : ℕ) (h : MirUp F K' 0) :
    ∃ ε ∈ bandChain F ((K' : ℝ) + 1),
      EdgeIs D ε (Q2 F 0 ((K' : ℝ) + 1)) (Q2 F (bcr e f) ((K' : ℝ) + 1)) := by
  obtain ⟨ha0, hb0, hc0, hbc, hac⟩ := consts F
  obtain ⟨hbr0, -, hbrcb⟩ := bcr_facts F
  obtain ⟨hcb0, -⟩ := cb_pos F
  obtain ⟨M, hM, hP⟩ := h
  simp only [Nat.cast_zero, zero_add] at hM hP
  have hC : Q2 F (bcr e f) ((K' : ℝ) + 1)
      = Lam F ((K' : ℝ) + 1 + bcr e f * (1 + cb e f)) (-(bcr e f)) := by
    simp only [Q2]; congr 1; ring
  have hMe : M = Q2 F (bcr e f) ((K' : ℝ) + 1) := by
    rw [hC]
    refine mirror_ident (Lam_ne F FC (Or.inr (by norm_num)))
      (Lam_ne F FC (Or.inr (by intro h; linarith))) hM ?_ ?_
    · have l1 : dist (Lam F ((K' : ℝ) + 1 + bcr e f * (1 + cb e f)) (-(bcr e f)))
          (Lam F ((K' : ℝ) + 1) 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := bcr e f * (1 + cb e f)) (q := bcr e f * (-1)) (by ring) (by ring),
          ← vec_smul, norm_smul, norm_V, Real.norm_of_nonneg hbr0.le, bcr,
          div_mul_cancel₀ _ hc0.ne']
      have r1 : dist (Lam F (K' : ℝ) 0) (Lam F ((K' : ℝ) + 1) 0) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := -1) (q := 0) (by ring) (by ring), norm_vec_m10]
      rw [l1, r1]
    · have l1 : dist (Lam F ((K' : ℝ) + 1 + bcr e f * (1 + cb e f)) (-(bcr e f)))
          (Lam F (K' : ℝ) 1) = (f : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := 1 + bcr e f * (1 + cb e f)) (q := -(bcr e f) - 1) (by ring)
          (by ring)]
        apply norm_of_sq hc0.le _ (norm_nonneg _)
        rw [norm_vec_sq, bcr, cb]
        have hf0 : (f : ℝ) ≠ 0 := (f_pos' F).ne'
        field_simp; ring
      have r1 : dist (Lam F (K' : ℝ) 0) (Lam F (K' : ℝ) 1) = (f : ℝ) ^ 2 := by
        rw [dist_Lam_eq F (p := 0) (q := -1) (by ring) (by ring),
          show vec F 0 (-1) = - vec F 0 1 by rw [vec_neg]; norm_num, norm_neg, norm_vec_01]
      rw [l1, r1]
  rw [hMe] at hP
  obtain ⟨iG, hrG⟩ := hP
  have e0 : Lam F ((K' : ℝ) + 1) 0 = Q2 F 0 ((K' : ℝ) + 1) := by simp [Q2]
  rw [e0] at hrG
  have hPt : Q2 F 0 ((K' : ℝ) + 1) ∈ Set.range (D.tile iG).pts := by rw [hrG]; exact mem3_1
  have hQt : Q2 F (bcr e f) ((K' : ℝ) + 1) ∈ Set.range (D.tile iG).pts := by rw [hrG]; exact mem3_3
  obtain ⟨m, hm⟩ := edge_idx hPt hQt (Q2_ne F FC (Or.inl (by intro h; linarith)))
  have hall : ∀ k, ellF F F.A + ((K' : ℝ) + 1) ≤ ellF F ((D.tile iG).pts k) := by
    intro k
    have : (D.tile iG).pts k ∈ Set.range (D.tile iG).pts := ⟨k, rfl⟩
    rw [hrG] at this
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h | h | h <;> rw [h]
    · rw [ellF_Q2 F FC]
    · rw [Lam, map_add, ellF_vec F FC]; linarith
    · rw [ellF_Q2 F FC]
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(iG, m), mem_bandChain F FC h1 h2 hall, by simp only [EdgeIs]; rw [h1, h2]⟩
  · exact ⟨(iG, m), mem_bandChain F FC h1 h2 hall,
      by simp only [EdgeIs]; rw [h1, h2, Set.pair_comm]⟩

/-- `σ_b` of R8's corner catalogue is the `Λ₂` swap at `kP′`. -/
theorem Sb_Sw (x : ℝ) : Sb F x = Sw F 0 x := by
  have e1 : Q2 F 0 x = Lam F x 0 := by simp [Q2]
  have e2 : Q2 F (0 + bcr e f) x = Lam F (x + ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 *
      (1 + cb e f)) (-(((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2)) := by
    simp only [Q2, bcr]; congr 1 <;> ring
  have e3 : Q2 F 0 (x + cb e f) = Lam F (x + cb e f) 0 := by simp [Q2]
  rw [Sw, e1, e2, e3]; rfl

/-- `T₂ + kP′` of R8's corner catalogue is `U(0, k)`. -/
theorem T2P_eq (FC : ApexPlacement.FrameCoords F) (K' : ℕ) :
    ({Lam F ((K' : ℝ) + 1) 0, Lam F ((K' : ℝ) + 1 + (1 + cb e f)) (-1), Lam F ((K' : ℝ) + 1 + 1) 0} :
      Set Plane) = T2c F 0 (K' + 1) := by
  rw [U_eq F FC]
  have e1 : Q2 F ((0 : ℕ) : ℝ) ((K' + 1 : ℕ) : ℝ) = Lam F ((K' : ℝ) + 1) 0 := by
    simp only [Q2]; push_cast; congr 1 <;> ring
  have e2 : Q2 F (((0 : ℕ) : ℝ) + 1) ((K' + 1 : ℕ) : ℝ)
      = Lam F ((K' : ℝ) + 1 + (1 + cb e f)) (-1) := by
    simp only [Q2]; push_cast; congr 1 <;> ring
  have e3 : Q2 F ((0 : ℕ) : ℝ) (((K' + 1 : ℕ) : ℝ) + 1) = Lam F ((K' : ℝ) + 1 + 1) 0 := by
    simp only [Q2]; push_cast; congr 1 <;> ring
  rw [e1, e2, e3]

/-! ## §2 S4(k) -/

set_option maxHeartbeats 4000000 in
/-- **S4(k) — PATCH COMPLETENESS IN THE `L_c` PHASE, frame form — PROVED (by composition, with the
repaired kill order).**  Level `K = K' + 1 ≤ f − 2` (every use in the (H) tree has `k ≤ n − 1 ≤ f − 2`;
the instance `k = n = f − 1`, possible only when `e² < f`, is not used and not formalized here), with
`Kc < fb` and `Π(K) = K·T₂ ∪ K·T₃` present (this contains `T₂ + jV`, `j < K`): Lemma G holds at level
`K` and every cell of `Π(K+1)` except the `α`-tile at `KV` is a tile:
* every `AD_K` far tile is the half-turn `D(i,t) = K + iV + tP′` (`i + t = K − 1`; at `i = K − 1` this
  is Lemma G at level `K`: `K + (K−1)V`);
* every row-`K` far tile is the half-turn `Z₀ + Λ(i,t)`;
* every `Λ₂` up cell of level `K + 1` except `T₂ + KV` (`U(i,t)`, `i + t = K`, `i ≤ K − 1`);
* every `Λ₃` up cell of level `K + 1` (`T₃ + Λ(i,t)`, `i + t = K`).
The conclusion does not depend on the tile at `KV` (review B repair R2): none is assumed. -/
theorem s4_frame (L : LFrame F) (K' : ℕ) (hKf : K' + 3 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hUp : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Dn F i t)) :
    (∀ i t, i + t = K' → Present D (Kc F i t)) ∧
    (∀ i t, i + t = K' → Present D (Dn F i t)) ∧
    (∀ i t, i + t = K' + 1 → i ≤ K' → Present D (T2c F i t)) ∧
    (∀ i t, i + t = K' + 1 → Present D (Up F i t)) := by
  classical
  have FC := L.FC
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  have hbc : (0 : ℝ) < ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (f : ℝ) ^ 2 := by positivity
  have hKf2 : K' + 2 ≤ f := by omega
  have hcol : ∀ j < K' + 1, Present D (Col F j) := fun j hj => by
    rw [Col_T2c]; exact hT2 0 j (by omega)
  -- (1) `AD_K`: a mirror forces `N_K` (PROP), which PK·a(K) kills
  obtain ⟨-, had2, had3⟩ := r8_ad F L K' hKf2 hKc hT2 hK2 (hUp K' 0 (by omega))
  have hNK : ¬ MirT2 F (K' + 1) 0 := fun h =>
    pka_frame F L (K' + 1) (by omega) (by omega) hcol (mirT2_Nq F FC K' h)
  have hAD : ∀ i t, i + t = K' → Present D (Kc F i t) := by
    intro i t hit
    rcases had2 i t (by omega) with h | h
    · exact h
    · exact absurd (had3 i t (by omega) h) hNK
  -- P2(K) at `X = KP′` (its (P2-b) is `K·T₂` plus the `AD_K` half-turns of step (1))
  have hP2cells : P2Inv F (K' + 1) (K' + 1) := by
    intro i t ht hit
    refine ⟨hT2 i t hit, ?_⟩
    rcases Nat.lt_or_ge (i + t + 2) (K' + 2) with h | h
    · exact hK2 i t (by omega)
    · exact hAD i t (by omega)
  have hP2 : ∀ ε ∈ bandChain F ((K' : ℝ) + 1),
      EdgeIs D ε (Q2 F 0 ((K' : ℝ) + 1)) (Q2 F (bcr e f) ((K' : ℝ) + 1)) → False := by
    intro ε hε hE
    apply p2_frame F L (K' + 1) (K' + 1)
    refine ⟨by omega, le_rfl, ?_, hP2cells⟩
    push_cast
    rw [sub_self, zero_add]
    exact ⟨ε, hε, hE⟩
  -- (2) row `K`: a mirror forces `G_K` (PROP), which P2(K) kills
  have hGK : ¬ MirUp F K' 0 := fun h => by
    obtain ⟨ε, hε, hE⟩ := mirUp_seed F FC K' h
    exact hP2 ε hε hE
  obtain ⟨-, hrow2, hrow3⟩ := r8_row F L K' hKf2 hUp hDn (hcol K' (by omega))
  have hROW : ∀ i t, i + t = K' → Present D (Dn F i t) := by
    intro i t hit
    rcases hrow2 i t hit with h | h
    · exact h
    · exact absurd (hrow3 i t hit h) hGK
  -- the Λ₃ cells above row `K + 1` that RW's hypotheses need
  have hC3 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t) ∧ Present D (Dn F i t) := by
    intro i t hit
    refine ⟨hUp i t hit, ?_⟩
    rcases Nat.lt_or_ge (i + t + 2) (K' + 2) with h | h
    · exact hDn i t (by omega)
    · exact hROW i t (by omega)
  -- (3) the corner `KP′`: the six fills
  obtain ⟨hT2P, hT3P⟩ : Present D (T2c F 0 (K' + 1)) ∧ Present D (Up F (K' + 1) 0) := by
    rcases r8_corner F L K' hKf2 hKc hT2 hK2 hUp hDn with ⟨-, -, h3, h4⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · refine ⟨?_, ?_⟩
      · rcases h3 with h | h
        · rw [T2P_eq F FC K'] at h; exact h
        · exfalso
          rw [Sb_Sw F] at h
          obtain ⟨ε, hε, hE⟩ := seed_of_Sw F FC 0 ((K' : ℝ) + 1) h
          rw [zero_add] at hE
          exact hP2 ε hε hE
      · rcases h4 with h | h
        · exact h
        · -- `σ_3`: RW(K) with C(K,K)
          exfalso
          obtain ⟨ε, hε, hE⟩ := seed_of_Xs F L _ _ h
          rw [zero_add] at hE
          apply rw_frame F L (K' + 1) (K' + 1) (by omega) le_rfl (by omega)
          refine ⟨fun i t hi ht => hC3 i t ht, ?_, ?_⟩
          · push_cast; exact start_of_edge F L _ _ hbc hε hE
          · push_cast
            exact ⟨ε, hε, 0, le_rfl, by simp, by rw [zero_add]; exact hE⟩
    · exact absurd h hNK
    · exact absurd h hGK
  refine ⟨hAD, hROW, ?_, ?_⟩
  · -- (4) the `Λ₂` slots of level `K + 1`
    intro i t hit hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : t = K' + 1 := by omega
      subst this; exact hT2P
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    have hA := hK2 a b (by omega)
    rcases slot2 F L a b (D_vertex_int F L hA) hA (hT2 a (b + 1) (by omega))
        (hAD (a + 1) b (by omega)) (hT2 (a + 1) b (by omega)) (hAD a (b + 1) (by omega)) with h | hSw
    · exact h
    · -- the swap: a b-seed on `ℓ_{b+1}`, killed by P2(b+1) with `n_X = K`
      exfalso
      obtain ⟨ε, hε, hE⟩ := seed_of_Sw F FC _ _ hSw
      apply p2_frame F L (b + 1) (K' + 1)
      refine ⟨by omega, by omega, ?_, fun i' t' ht' hit' => hP2cells i' t' (by omega) hit'⟩
      have e1 : (((K' + 1 : ℕ) : ℝ) - ((b + 1 : ℕ) : ℝ)) = (a : ℝ) + 1 := by
        have : ((a + 1 + (b + 1) : ℕ) : ℝ) = ((K' + 1 : ℕ) : ℝ) := by rw [hit]
        push_cast at this ⊢; linarith
      rw [e1]; push_cast; exact ⟨ε, hε, hE⟩
  · -- (4)–(5) the `Λ₃` slots of level `K + 1`
    intro i t hit
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · -- the leg slot `J_K` (lem:sidenob, **m = 1**)
      have : t = K' + 1 := by omega
      subst this
      exact slot_leg F L K' hKf (hUp 0 K' (by omega)) (hROW 0 K' (by omega))
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · have : i = K' + 1 := by omega
      subst this; exact hT3P
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    rcases slot_int F L a b (by omega) (hDn a b (by omega)) (hUp (a + 1) b (by omega))
        (hROW a (b + 1) (by omega)) (hUp a (b + 1) (by omega)) (hROW (a + 1) b (by omega))
      with h | hXs
    · exact h
    · -- the swap: C(a+1, K), killed by RW(a+1)
      exfalso
      apply rw_frame F L (a + 1) (K' + 1) (by omega) (by omega) (by omega)
      refine ⟨fun i' t' hi' ht' => hC3 i' t' ht', ?_, ?_⟩
      · exact start_of_up F L (a + 1) (hUp (a + 1) 0 (by omega))
      · obtain ⟨ε, hε, hE⟩ := seed_of_Xs F L _ _ hXs
        refine ⟨ε, by push_cast; exact hε, (b : ℝ) + 1, by positivity, ?_, by push_cast; exact hE⟩
        have : ((a + 1 + (b + 1) : ℕ) : ℝ) = ((K' + 1 : ℕ) : ℝ) := by rw [hit]
        push_cast at this ⊢; linarith

/-! ## §3 R9 and S5 + S5-M -/

/-- **R9 — the `L_c` phase: `Π(k) → Π(k+1)` — PROVED (S4(k) plus `L_c`).**  If `Π(K)` is present,
`Kc < fb`, `K ≤ f − 2`, and the `α`-tile at `KV` is `L_c = T₂ + KV`, then `Π(K+1)` is present. -/
theorem r9_frame (L : LFrame F) (K' : ℕ) (hKf : K' + 3 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hUp : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Dn F i t))
    (hLc : Present D (T2c F (K' + 1) 0)) :
    (∀ i t, i + t + 1 ≤ K' + 2 → Present D (T2c F i t)) ∧
    (∀ i t, i + t + 2 ≤ K' + 2 → Present D (Kc F i t)) ∧
    (∀ i t, i + t + 1 ≤ K' + 2 → Present D (Up F i t)) ∧
    (∀ i t, i + t + 2 ≤ K' + 2 → Present D (Dn F i t)) := by
  obtain ⟨hAD, hROW, hS2, hS3⟩ := s4_frame F L K' hKf hKc hT2 hK2 hUp hDn
  refine ⟨fun i t hit => ?_, fun i t hit => ?_, fun i t hit => ?_, fun i t hit => ?_⟩
  · rcases Nat.lt_or_ge (i + t + 1) (K' + 2) with h | h
    · exact hT2 i t (by omega)
    · rcases Nat.lt_or_ge i (K' + 1) with hi | hi
      · exact hS2 i t (by omega) (by omega)
      · have : i = K' + 1 := by omega
        have ht : t = 0 := by omega
        subst this; subst ht; exact hLc
  · rcases Nat.lt_or_ge (i + t + 2) (K' + 2) with h | h
    · exact hK2 i t (by omega)
    · exact hAD i t (by omega)
  · rcases Nat.lt_or_ge (i + t + 1) (K' + 2) with h | h
    · exact hUp i t (by omega)
    · exact hS3 i t (by omega)
  · rcases Nat.lt_or_ge (i + t + 2) (K' + 2) with h | h
    · exact hDn i t (by omega)
    · exact hROW i t (by omega)

set_option maxHeartbeats 2000000 in
/-- **S5 + S5-M — THE PURE-CHAIN END — PROVED** (proof_H_empty.md §5.13; proof_L3M.md §7).  Let
`n = n' + 1` be the chain length (`nc < fb < (n+1)c`) and suppose `Π(n)` is present (it contains the
`L_c` chain `T₂ + jV`, `j < n`, and `T₃ + (n−1)P′`).  Then there is no such dissection:
* S5-M: the tile across the `r`-end edge of `AD_n` is `K + (n−1)V`, not the mirror `M_n`, since a
  mirror on `AD_n` forces `N_n` (`r8_ad`, PROP) and PK·a(n) kills `N_n` (`pka_frame`);
* S5: `nV` is pierced (Lemma A, **m = 1**) and closes with the `β` of `T₂ + (n−1)V` and the `γ` of
  `K + (n−1)V` to a residual `α`: its tile is `L_c` or `L_b` (`chain_alpha`), and each has a vertex at
  depth `(n+1)c > fb` (if `d* < b`, `K + (n−1)V` itself already has its vertex `nV + P′` outside:
  that branch is the same contradiction, reached earlier). -/
theorem s5_frame (L : LFrame F) (n' : ℕ)
    (hnc : ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hnc1 : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((n' + 2 : ℕ) : ℝ) * (f : ℝ) ^ 2)
    (hT2 : ∀ i t, i + t + 1 ≤ n' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ n' + 1 → Present D (Kc F i t))
    (hU : Present D (Up F n' 0)) : False := by
  classical
  have FC := L.FC
  obtain ⟨-, hb0, hc0, -, -⟩ := consts F
  obtain ⟨hcb0, hcb1⟩ := cb_pos F
  have hf0 : (0 : ℝ) < f := f_pos' F
  have hnf : n' + 2 ≤ f := by
    have h1 : ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * (f : ℝ) ^ 2 := by
      have : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < (f : ℝ) * (f : ℝ) ^ 2 := by
        have : (0 : ℝ) < (e : ℝ) ^ 2 := by
          have : (2 : ℝ) ≤ e := by exact_mod_cast F.he
          positivity
        nlinarith
      linarith
    have h2 : ((n' + 1 : ℕ) : ℝ) < f := lt_of_mul_lt_mul_right h1 (by positivity)
    have : n' + 1 < f := by exact_mod_cast h2
    omega
  have hcol : ∀ j < n' + 1, Present D (Col F j) := fun j hj => by
    rw [Col_T2c]; exact hT2 0 j (by omega)
  obtain ⟨-, had2, had3⟩ := r8_ad F L n' hnf hnc hT2 hK2 hU
  -- S5-M: the `r`-end tile is the half-turn `K + (n−1)V`
  have hKn : Present D (Kc F n' 0) := by
    rcases had2 n' 0 (by omega) with h | h
    · exact h
    · exact absurd (mirT2_Nq F FC n' (had3 n' 0 (by omega) h))
        (fun hN => pka_frame F L (n' + 1) (by omega) (by omega) hcol hN)
  -- S5: the residual `α` at `nV` is `L_c` or `L_b`; both reach depth `(n+1)c > fb`
  have hout : ∀ x : Plane, x = Q2 F ((n' : ℝ) + 1 + 1) 0 ∨ x = Q2 F ((n' : ℝ) + 1) (cb e f) →
      x ∉ D.target.carrier := by
    intro x hx hm
    have hle : ((n' : ℝ) + 1 + 1) * cb e f ≤ f := by
      rcases hx with rfl | rfl
      · have := Q2_le F FC hm; linarith
      · have := Q2_le F FC hm; linarith
    have h1 : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((n' : ℝ) + 1 + 1) * (f : ℝ) ^ 2 := by
      push_cast at hnc1; linarith
    have h2 : ((n' : ℝ) + 1 + 1) * cb e f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)
        = ((n' : ℝ) + 1 + 1) * (f : ℝ) ^ 2 := by
      rw [cb]; field_simp
    nlinarith
  rcases chain_alpha F L n' (fun i hi => hT2 i 0 (by omega)) hKn with h | h
  · apply hout (Q2 F ((n' : ℝ) + 1 + 1) 0) (Or.inl rfl)
    apply mem_of_present h
    rw [U_eq F FC]; push_cast; exact mem3_2
  · apply hout (Q2 F ((n' : ℝ) + 1) (cb e f)) (Or.inr rfl)
    apply mem_of_present h
    rw [Sw, zero_add]; exact mem3_3

/-! ## §4 For real dissections -/

/-- **S4(k) FOR EVERY APEX FRAME OF A REAL `m = 1` DISSECTION — PROVED** (by composition). -/
theorem s4_real_all {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk)
    (FC : ApexPlacement.FrameCoords F) (K' : ℕ) (hKf : K' + 3 ≤ f)
    (hKc : ((K' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hT2 : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Kc F i t))
    (hUp : ∀ i t, i + t + 1 ≤ K' + 1 → Present D (Up F i t))
    (hDn : ∀ i t, i + t + 2 ≤ K' + 1 → Present D (Dn F i t)) :
    (∀ i t, i + t = K' → Present D (Kc F i t)) ∧
    (∀ i t, i + t = K' → Present D (Dn F i t)) ∧
    (∀ i t, i + t = K' + 1 → i ≤ K' → Present D (T2c F i t)) ∧
    (∀ i t, i + t = K' + 1 → Present D (Up F i t)) :=
  s4_frame F (lframe_real F h FC) K' hKf hKc hT2 hK2 hUp hDn

/-- **S5 + S5-M FOR EVERY APEX FRAME OF A REAL `m = 1` DISSECTION — PROVED.** -/
theorem s5_real_all {kk : Fin 3} (h : ApexFrameReal.M1Data D e f α β γ kk)
    (FC : ApexPlacement.FrameCoords F) (n' : ℕ)
    (hnc : ((n' + 1 : ℕ) : ℝ) * (f : ℝ) ^ 2 < (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hnc1 : (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < ((n' + 2 : ℕ) : ℝ) * (f : ℝ) ^ 2)
    (hT2 : ∀ i t, i + t + 1 ≤ n' + 1 → Present D (T2c F i t))
    (hK2 : ∀ i t, i + t + 2 ≤ n' + 1 → Present D (Kc F i t))
    (hU : Present D (Up F n' 0)) : False :=
  s5_frame F (lframe_real F h FC) n' hnc hnc1 hT2 hK2 hU

end Erdos634.Draft.RowWallReal

#print axioms Erdos634.Draft.RowWallReal.mirror_ident
#print axioms Erdos634.Draft.RowWallReal.mirT2_Nq
#print axioms Erdos634.Draft.RowWallReal.mirUp_seed
#print axioms Erdos634.Draft.RowWallReal.s4_frame
#print axioms Erdos634.Draft.RowWallReal.r9_frame
#print axioms Erdos634.Draft.RowWallReal.s5_frame
#print axioms Erdos634.Draft.RowWallReal.s4_real_all
#print axioms Erdos634.Draft.RowWallReal.s5_real_all
