/-
Draft/SideRunGCornerRules.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module R1 (geometry, first file) of the plan for
`thm:cornerrun`: the geometric tools of the rules of the side from a corner `A'` of angle `2α` or `3α` to a corner `Q'` of angle `β` or `α + β`
(`CornersA`).  The word part is `Draft/SideRunGCornerWords.lean`; the rules themselves and the final statement are in `Draft/SideRunGCornerSide.lean`.

WHY NEW LEMMAS.  `side_rulesG` (`Draft/SideRunGRules.lean`) is stated for `CornersG`: the left corner is `β` or `α + β`, the RIGHT corner is `β`.  Here the right corner may be `α + β`
(`CornersA.hQ`), and the runs that follow a tile showing `γ` begin at an arbitrary point `X i` of the side.  So:
* `corner_two_alpha_gen`: **no two tiles show `α` at a corner `α + β`** (any vertex of the target; `SetupG.corner_two_alpha` is for `(0,0)`).
* `hch_cornerR`, `K1_of_cornerR`: **the chords and (K1) at the RIGHT corner `α + β`** (`ε = -1`, `x = L`), the mirror images of `hch_corner`, `K1_of_corner` (paper, the mirror statement `L'_k`, condition `(i')`: "`R` is the right end of `s` and a
  corner `α + β` (the second tile there shows `β`)").
* `K3G_run_end_gen`: **(K3) at the right end of a run of `C1` that starts at any tile of the chain** (`K3G_run_end` of `Draft/SideRunGCornerRun.lean` is for the run from `A'`): the right corner `β` (`K3G_out_right`) or `α + β`
  (`bad_corner_right`), or a next tile other than `B1`, `C1` (`bad_nb`).  `kill_C1A`: the run lemma `L_k` for a run of `C1` (paper: the run lemma, conditions (i), (ii)).
* `kill_C2A_core`, `kill_C2A`, `kill_C2A_end`: the mirror run lemma `L'_k` for a run of `C2` that follows a tile showing `γ` (condition (ii')), ending before a tile (`kill_C2G`, case "the tile before the run shows `γ`"), or at the right end `Q'`
  of angle `α + β` (condition (i')).  At a right corner `β` a run of `C2` cannot end the side: the last tile would show `α` at a corner that one tile fills with `β` (`corner_tile_beta`).

WITNESSES.  As in `Draft/SideRunGCornerRun.lean`: the statements conclude `False` (or (K3)) under the conditions of the run lemma; `CornersA` is satisfied by the real tilings of the member `(2,3)` (the corners `2α`, `β`/`α + β` of `W_M`).

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGCornerWords
import Erdos634.Draft.SideRunGCornerRun

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. The right corner `α + β` -/

section rightcorner

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **A corner `α + β` of the target (any vertex) does not carry two tiles showing `α`** (`corner_counts`: the tile angles are `a α + b β`, `Σ a = 1`; a tile showing `α` has `a = 1`). -/
theorem corner_two_alpha_gen (S : SetupG D e f α β γ L ax ay) (k : Fin 3)
    (hk : D.target.localAngle (D.target.pts k) = α + β) {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (D.target.pts k) = α) (hj : (D.tile j).localAngle (D.target.pts k) = α) :
    False := by
  obtain ⟨a, b, hab, -, -, -, ha, hb⟩ := corner_counts S k (A := 1) (B := 1) (by rw [hk]; simp)
  have ha1 : ∀ m, (D.tile m).localAngle (D.target.pts k) = α → a m = 1 := by
    intro m hm
    have h1 := hab m
    rw [hm] at h1
    obtain ⟨hp, hq⟩ := ab_zero S.hA (p := (a m : ℤ) - 1) (q := (b m : ℤ))
      (by push_cast; linear_combination (-1 : ℝ) * h1)
    omega
  have h5 : ∑ x ∈ ({i, j} : Finset (Fin N)), a x = a i + a j := Finset.sum_pair hij
  have h6 : ∑ x ∈ ({i, j} : Finset (Fin N)), a x ≤ ∑ x, a x :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h7 := ha1 i hi
  have h8 := ha1 j hj
  omega

/-- **the chords from the corner `Q' = (L, 0)` of angle `α + β` are interior to the target** (`ε = -1`; the mirror image of `hch_corner`) -/
theorem hch_cornerR (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t) (hax : ax = L - t * (e : ℝ))
    (hay' : ay = t * rtG (e : ℝ) (f : ℝ)) (hP : mkPt L 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) (-1) L 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) (-1) L 0 0) (lpG (e : ℝ) (f : ℝ) (-1) L 0 j)
        ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lpG_zero]
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hhp := hhG_pos he0 hef
  have hu := uuG_spec he0 hef
  have hh' := hhG_spec he0 hef
  have hrt := rtG_pos he0 hef
  have hb := S.b_pos
  have key : 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))
      - (e : ℝ) * hhG (e : ℝ) (f : ℝ))
      = 2 * rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by
    linear_combination (-(rtG (e : ℝ) (f : ℝ))) * hu - (e : ℝ) * hh'
  have hX : 0 < rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))
      - (e : ℝ) * hhG (e : ℝ) (f : ℝ) := by
    have h2 : 0 < 2 * rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 := by positivity
    rw [← key] at h2
    have h2f := two_f2_pos he0 hef
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonneg h2f.le (neg_nonneg.mpr hneg)]
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inl ?_) (Or.inr ?_)
  · rw [lpG_snd]; exact mul_pos hjpos hhp
  · rw [gA_mk]; nlinarith [mul_pos S.hay S.hL]
  · unfold lpG
    rw [gB_mk, hax, hay']
    have hpos := mul_pos (mul_pos ht hjpos) hX
    nlinarith [hpos]

/-- **(K1) at the right corner `Q' = (L, 0)` of angle `α + β`** (`ε = -1`; the mirror image of `K1_of_corner`): no tile of the side `σ` has the vertices `Q'` and `p(0,1)`, given the tile `t₀ = U(0, 0)` of the lattice with
origin `Q'` (a tile of the run that shows `α` at `Q'`). -/
theorem K1_of_cornerR (S : SetupG D e f α β γ L ax ay)
    (hQ : D.target.localAngle (mkPt L 0) = α + β) {t₀ : Fin N}
    (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) (-1) L 0 0) (lpG (e : ℝ) (f : ℝ) (-1) L (0 + 1) 0)
      (lpG (e : ℝ) (f : ℝ) (-1) L 0 (0 + 1))) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lpG (e : ℝ) (f : ℝ) (-1) L 0 0 →
      (D.tile t').pts m = lpG (e : ℝ) (f : ℝ) (-1) L 0 1 →
      (∀ i, FXG (e : ℝ) (f : ℝ) (-1) ((D.tile t').pts i) ≤ lvG (e : ℝ) (f : ℝ) (-1) L 0) → False := by
  intro t' k m hkm hk hm hle
  have hε : ((-1 : ℝ)) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hP : lpG (e : ℝ) (f : ℝ) (-1) L 0 0 = mkPt L 0 := lpG_zero _ _ _ _
  have ht0 : t' ≠ t₀ := by
    obtain ⟨i, hi⟩ := h0.idx₂
    refine ne_of_F (FXG (e : ℝ) (f : ℝ) (-1)) hle (i := i) ?_
    rw [hi, FXG_lp hε]
    exact lvG_lt he0 hef (by norm_num)
  have hd : dist ((D.tile t').pts k) ((D.tile t').pts m) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    rw [hk, hm]
    have := dist_step_vG (x := L) he0 hef hε 0 0
    rwa [zero_add] at this
  have hang := b_edge_angleG S.tile S.hM hkm hd
  rw [hk, hP] at hang
  rcases hang with hγ' | hα'
  · have h1 := one_angle_le D.toDissection (mkPt L 0) t'
    rw [hγ', hQ] at h1
    linarith
  · have ha0 := (U_anglesG S hε h0).1
    rw [hP] at ha0
    exact corner_two_alpha_gen S 1 (by rw [S.B_eq]; exact hQ) ht0 (by rw [S.B_eq]; exact hα')
      (by rw [S.B_eq]; exact ha0)

end rightcorner

/-! ## 2. (K3) at the right end of a run of `C1`, and the run lemma `L_k` -/

section runc1

variable {e f : ℕ} {α β γ L ax ay : ℝ} {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- **(K3) at the right end `R` of a run of `k` tiles `C1` that starts at the tile `i` of the chain**: the right corner is `β` (`K3G_out_right`) or `α + β` (`bad_corner_right`), or the next tile of the chain is not `B1`, `C1`
(`bad_nb`).  (`K3G_run_end` for a run that does not start at `A'`.) -/
theorem K3G_run_end_gen (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C1)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) :
    K3G D (e : ℝ) (f : ℝ) 1 (X i) (k : ℝ) 0 := by
  have C : CtxBase D e f α β γ L ax ay 1 (X i) := ⟨S, Or.inl rfl⟩
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hc := S.c_pos
  have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hxR : X (i + k) = X i + (k : ℝ) * (f : ℝ) ^ 2 := hpos k le_rfl
  have hk0 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
  have hlast := Ch.htile (i + (k - 1)) (by omega)
  rw [hrun (k - 1) (by omega)] at hlast
  have hposl := hpos (k - 1) (by omega)
  rw [hk0] at hposl
  have hU := S.c1_lpG (x := X i) (ξ := (k : ℝ) - 1) hlast hposl
  have hG1 : 0 < (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) 1 := by
    rw [lpG_snd]; linarith
  have hA₀ : (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) 0) 1 = 0 := by rw [lpG_snd]; ring
  have eV : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0 = mkPt (X (i + k)) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have eA : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) 0 = mkPt (X (i + k) - (f : ℝ) ^ 2) 0 := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have eG : lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)
      = mkPt (X (i + k) - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) := by
    unfold lpG; exact mkPt_congr (by rw [hxR]; ring) (by ring)
  have hβ0 : (D.tile (tile (i + (k - 1)))).localAngle (mkPt (X (i + k)) 0) = β := by
    have e' : X (i + (k - 1)) + Ty.lenG (e : ℝ) (f : ℝ) Ty.C1 = X (i + k) := by
      show X (i + (k - 1)) + (f : ℝ) ^ 2 = _
      rw [hposl, hxR]; ring
    have h := (S.angles hlast).2
    rw [e'] at h
    exact h
  have hU' := hU
  rw [eV] at hU'
  rcases hsucc with hend | ⟨hlt, hZ1, hZ2⟩
  · -- the run ends at the corner `Q'`
    have hXL : X (i + k) = L := by rw [hend]; exact Ch.hXm
    rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
    · exact S.K3G_out_right ht hax hay (by linarith)
    · have hQ := corner_right_ab S ht hax hay
      have hRmem : mkPt L 0 ∈ D.target.carrier := by
        rw [← hXL, ← eV]; exact hU.mem₂
      have hGmem : mkPt (L - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) ∈ D.target.carrier := by
        rw [← hXL, ← eG]; exact hU.mem₃
      have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0)
          (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
        rw [eV, eG, hXL]
        exact hint_right_ab S ht hax hay hRmem hGmem
      refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
      rw [eV, hXL] at hW hθ
      rw [hXL] at hU' hβ0
      exact bad_corner_right S hQ hG1 hU' hA₀ hβ0 hW hθ hZ
  · -- the run ends before a tile other than `B1`, `C1`
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hlt
    have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1 + 1) 0)
        (lpG (e : ℝ) (f : ℝ) 1 (X i) ((k : ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
      rw [eV]
      refine S.interior_seg (Ch.mem hlt) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
      · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
      · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]
    have hj := Ch.htile (i + k) hlt
    have hjang := (S.angles hj).1
    have hlenpos := Ty.lenG_pos he0 hef (τ (i + k))
    obtain ⟨T, hT⟩ : ∃ T, τ (i + k) = T := ⟨_, rfl⟩
    rw [hT] at hZ1 hZ2 hjang
    have hθj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ ∨
        (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = β := by
      rw [hjang]
      cases T
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact absurd rfl hZ1
      · exact Or.inl rfl
      · exact absurd rfl hZ2
      · exact Or.inr rfl
    obtain ⟨kj, mj, jj, -, -, -, -, hmj, -, -⟩ := hj
    refine C.K3G_of_next hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV] at hW hθ
    refine S.bad_nb hx0 hxL hG1 hU' hA₀ hβ0 hmj (mkPt_one _ _)
      (mkPt_ne_of_fst (by linarith)) ?_ hθj hW hθ hZ
    rw [eA]; exact mkPt_ne_of_fst (by linarith)

/-- **`L_k` for a run of `C1`** (paper: the run lemma, conditions (i) and (ii)): a run of `k < f` tiles `C1` with (K1) at its first end that ends at the right corner `Q'` or before a tile other than `B1`, `C1` does not exist. -/
theorem kill_C1A (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (Ch : ChainG D e f L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkf : k < f) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C1) {x : ℝ} (hxi : X i = x)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lpG (e : ℝ) (f : ℝ) 1 x 0 0 →
      (D.tile t').pts m' = lpG (e : ℝ) (f : ℝ) 1 x 0 1 →
      (∀ i', FXG (e : ℝ) (f : ℝ) 1 ((D.tile t').pts i') ≤ lvG (e : ℝ) (f : ℝ) 1 x 0) → False)
    (hch : ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 x 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 x 0 0) (lpG (e : ℝ) (f : ℝ) 1 x 0 j) ⊆ interior D.target.carrier)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) : False := by
  subst hxi
  have C : CtxG D e f α β γ L ax ay 1 (X i) := ⟨⟨S, Or.inl rfl⟩, hK1, hch⟩
  have hpos := Ch.run_pos (T := Ty.C1) (c := (f : ℝ) ^ 2) rfl hik hrun
  have hUT : ∀ j : ℕ, j < k → UTG D (e : ℝ) (f : ℝ) 1 (X i) j 0 := by
    intro j hj
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj] at h
    exact ⟨tile (i + j), S.c1_lpG h (hpos j hj.le)⟩
  exact C.run_diesG hk1 hkf hUT (K3G_run_end_gen S Co Ch hk1 hik hrun hsucc)

end runc1

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.corner_two_alpha_gen
#print axioms Erdos634.Draft.SideRunGA.hch_cornerR
#print axioms Erdos634.Draft.SideRunGA.K1_of_cornerR
#print axioms Erdos634.Draft.SideRunGA.K3G_run_end_gen
#print axioms Erdos634.Draft.SideRunGA.kill_C1A
