/-
Draft/SideRunRules.lean -- Stage 4b of the formalization of the side theorem of room GAP3: the word rules and the
SIDE THEOREM ((private working notes, not included), section 3).

* `Corners n L ax ay`: the corner `B` of the target `Q = (0,0)`, `B = (L,0)`, `A = (ax, ay)` has angle `β` (the side
  `BA` runs along the `a`-edge of a `C1` tile), and the corner `Q` has angle `β` (first form) or `α + β` (second
  form: the side `QA` has the direction `(1, √(4n²−1))`);
* `Chain`: a typed chain of base tiles on `QB` (`Setup.typed_chain` gives one);
* `Setup.kill_C1`, `Setup.kill_C2`: a run of `k < n` tiles `C1` (resp. `C2`) with (K1) at its first end does not
  end at `B`, nor before a tile showing `γ` or `β` (resp. does not start at `Q`, nor after a tile showing `γ`);
* `Setup.side_rules`: the typed word of the side satisfies the rules `SideRules` of `SideRunWords`;
* `Setup.side_theorem`: **THE SIDE THEOREM** (both forms): the side carries `n` consecutive tiles of type `C1` or
  `n` consecutive tiles of type `C2`;
* `Setup.no_tiling_of_length`: if `L = M (κ n² − 1)` with `(κ − 1) M < n`, there is no such dissection.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunSources

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.Geometry.Dissection
  Erdos634.Draft.W2E1 Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay : ℝ}

/-- **The corners of the side `QB`**: angle `β` at `B`; angle `β` or `α + β` at `Q`. -/
structure Corners (n : ℕ) (L ax ay : ℝ) : Prop where
  hB : ∃ t : ℝ, 0 < t ∧ ax = L - t * uu n ∧ ay = t * hh n
  hQ : (∃ t : ℝ, 0 < t ∧ ax = t * uu n ∧ ay = t * hh n) ∨ (∃ t : ℝ, 0 < t ∧ ax = t ∧ ay = t * rt n)

/-- **A typed chain of base tiles on the side `QB`.** -/
structure Chain (D : CongruentDissection N) (n : ℕ) (L : ℝ) (m : ℕ) (X : ℕ → ℝ)
    (tile : ℕ → Fin N) (τ : ℕ → Ty) : Prop where
  hm0 : 0 < m
  hX0 : X 0 = 0
  hXm : X m = L
  hstep : ∀ k, k < m → X (k + 1) = X k + (τ k).lenR n
  htile : ∀ k, k < m → BaseTile D n (tile k) (τ k) (X k)

namespace Chain

variable {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

theorem nonneg (Ch : Chain D n L m X tile τ) (S : Setup D n α β γ L ax ay) {k : ℕ} (hk : k < m) :
    0 ≤ X k := (S.baseTile_range (Ch.htile k hk)).1

theorem lt_L (Ch : Chain D n L m X tile τ) (S : Setup D n α β γ L ax ay) {k : ℕ} (hk : k < m) :
    X k < L := by
  have h1 := (S.baseTile_range (Ch.htile k hk)).2
  have h2 := Ty.lenR_pos S.f2 (τ k)
  linarith

theorem prev (Ch : Chain D n L m X tile τ) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ m) :
    X (k - 1) + (τ (k - 1)).lenR n = X k := by
  have h1 := Ch.hstep (k - 1) (by omega)
  rw [Nat.sub_add_cancel hk0] at h1
  exact h1.symm

theorem pos (Ch : Chain D n L m X tile τ) (S : Setup D n α β γ L ax ay) {k : ℕ} (hk0 : 0 < k)
    (hk : k ≤ m) : 0 < X k := by
  have h1 := Ch.prev hk0 hk
  have h2 := Ch.nonneg S (k := k - 1) (by omega)
  have h3 := Ty.lenR_pos S.f2 (τ (k - 1))
  linarith

theorem mem (Ch : Chain D n L m X tile τ) {k : ℕ} (hk : k < m) :
    mkPt (X k) 0 ∈ D.target.carrier := by
  obtain ⟨k', m', j', -, -, -, hk', -, -, -⟩ := Ch.htile k hk
  rw [← hk']; exact pts_mem_target D.toDissection (tile k) k'

/-- the positions along a run of tiles of one type -/
theorem run_pos (Ch : Chain D n L m X tile τ) {T : Ty} {c : ℝ} (hc : T.lenR n = c) {i k : ℕ}
    (hik : i + k ≤ m) (hrun : ∀ j, j < k → τ (i + j) = T) :
    ∀ j, j ≤ k → X (i + j) = X i + j * c := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h := Ch.hstep (i + j) (by omega)
    rw [hrun j (by omega), hc] at h
    rw [← Nat.add_assoc, h, ih (by omega)]
    push_cast
    ring

end Chain

namespace Setup

variable {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}

/-- a `C1` tile as the lattice triangle `U(ξ, 0)` of the run to the right from `(x, 0)` -/
theorem c1_lp (S : Setup D n α β γ L ax ay) {t : Fin N} {x' x ξ : ℝ}
    (h : BaseTile D n t Ty.C1 x') (hx : x' = x + ξ * (n:ℝ) ^ 2) :
    HasV D t (lp n 1 x ξ 0) (lp n 1 x (ξ + 1) 0) (lp n 1 x ξ (0 + 1)) := by
  refine (S.c1_data h).congr ?_ ?_ ?_
  · unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)

/-- a `C2` tile as the lattice triangle `U(ξ, 0)` of the run to the left from `(x, 0)` -/
theorem c2_lp (S : Setup D n α β γ L ax ay) {t : Fin N} {x' x ξ : ℝ}
    (h : BaseTile D n t Ty.C2 x') (hx : x' = x - (ξ + 1) * (n:ℝ) ^ 2) :
    HasV D t (lp n (-1) x ξ 0) (lp n (-1) x (ξ + 1) 0) (lp n (-1) x ξ (0 + 1)) := by
  refine (S.c2_data h).congr ?_ ?_ ?_
  · unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)
  · unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)

theorem angleQ_le (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay) :
    D.target.localAngle (mkPt 0 0) ≤ α + β := by
  have hα := S.hA.hα
  rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
  · have h := (D.target).localAngle_vertex 0
    rw [S.corner_left_beta ht hax hay, S.Q_eq] at h
    rw [h]; linarith
  · exact (S.corner_left_ab ht hax hay).le

/-- **A run of `k < n` tiles `C1`** from `(x, 0)`, with (K1) there, does not end at `B` nor before a tile other than
`B1` and `C1`. -/
theorem kill_C1 (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay)
    (Ch : Chain D n L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hik : i + k ≤ m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C1) {x : ℝ} (hxi : X i = x)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lp n 1 x 0 0 →
      (D.tile t').pts m' = lp n 1 x 0 1 → (∀ i', FX n 1 ((D.tile t').pts i') ≤ lv n 1 x 0) → False)
    (hch : ∀ j : ℕ, 1 ≤ j → lp n 1 x 0 j ∈ D.target.carrier →
      openSegment ℝ (lp n 1 x 0 0) (lp n 1 x 0 j) ⊆ interior D.target.carrier)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) : False := by
  subst hxi
  have hf1 := S.f1
  have hhp := hh_pos hf1
  have hc := S.c_pos
  have C : Ctx D n α β γ L ax ay 1 (X i) := ⟨S, Or.inl rfl, hK1, hch⟩
  have hpos := Ch.run_pos (T := Ty.C1) (c := (n:ℝ) ^ 2) rfl hik hrun
  have hUT : ∀ j : ℕ, j < k → UT D n 1 (X i) j 0 := by
    intro j hj
    have h := Ch.htile (i + j) (by omega)
    rw [hrun j hj] at h
    exact ⟨tile (i + j), S.c1_lp h (hpos j hj.le)⟩
  refine C.run_dies hk1 hkn hUT ?_
  have hxR : X (i + k) = X i + k * (n:ℝ) ^ 2 := hpos k le_rfl
  rcases hsucc with hend | ⟨hlt, hZ1, hZ2⟩
  · obtain ⟨t, ht, hax, hay⟩ := Co.hB
    refine S.K3_out_right ht hax hay ?_
    rw [← hxR, hend, Ch.hXm]
  · have hk0 : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
    have hlast := Ch.htile (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega)] at hlast
    have hposl := hpos (k - 1) (by omega)
    rw [hk0] at hposl
    have hU := S.c1_lp hlast hposl
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hlt
    have eV : lp n 1 (X i) ((k:ℝ) - 1 + 1) 0 = mkPt (X (i + k)) 0 := by
      unfold lp; exact mkPt_congr (by rw [hxR]; ring) (by ring)
    have eA : lp n 1 (X i) ((k:ℝ) - 1) 0 = mkPt (X (i + k) - (n:ℝ) ^ 2) 0 := by
      unfold lp; exact mkPt_congr (by rw [hxR]; ring) (by ring)
    have hG1 : 0 < (lp n 1 (X i) ((k:ℝ) - 1) (0 + 1)) 1 := by rw [lp_one]; linarith
    have hint : openSegment ℝ (lp n 1 (X i) ((k:ℝ) - 1 + 1) 0) (lp n 1 (X i) ((k:ℝ) - 1) (0 + 1))
        ⊆ interior D.target.carrier := by
      rw [eV]
      refine S.interior_seg (Ch.mem hlt) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
      · rw [gA_mk]; nlinarith [mul_pos S.hay hx0]
      · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxL)]
    have hβ0 : (D.tile (tile (i + (k - 1)))).localAngle (mkPt (X (i + k)) 0) = β := by
      have e : X (i + (k - 1)) + Ty.lenR (n:ℝ) Ty.C1 = X (i + k) := by
        show X (i + (k - 1)) + (n:ℝ) ^ 2 = _
        rw [hposl, hxR]; ring
      have h := (S.angles hlast).2
      rw [e] at h
      exact h
    have hj := Ch.htile (i + k) hlt
    have hjang := (S.angles hj).1
    have hlenpos := Ty.lenR_pos S.f2 (τ (i + k))
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
    have hU' := hU
    rw [eV] at hU'
    refine C.K3_of_next hkn hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV] at hW hθ
    refine S.bad_nb hx0 hxL hG1 hU' (by rw [lp_one]; ring) hβ0 hmj (mkPt_one _ _)
      (mkPt_ne_of_fst (by linarith)) ?_ hθj hW hθ hZ
    rw [eA]; exact mkPt_ne_of_fst (by linarith)

/-- **A run of `k < n` tiles `C2`** ending at `(X (i+k), 0)`, with (K1) there, does not start at `Q` nor after a tile
showing `γ`. -/
theorem kill_C2 (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay)
    (Ch : Chain D n L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hik : i + k < m)
    (hrun : ∀ j, j < k → τ (i + j) = Ty.C2)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lp n (-1) (X (i + k)) 0 0 →
      (D.tile t').pts m' = lp n (-1) (X (i + k)) 0 1 →
      (∀ i', FX n (-1) ((D.tile t').pts i') ≤ lv n (-1) (X (i + k)) 0) → False)
    (hpred : i = 0 ∨ (τ (i - 1)).gR) : False := by
  have hf1 := S.f1
  have hhp := hh_pos hf1
  have hc := S.c_pos
  have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
  have hxL : X (i + k) < L := Ch.lt_L S hik
  have C : Ctx D n α β γ L ax ay (-1) (X (i + k)) :=
    ⟨S, Or.inr rfl, hK1, S.hch_pos hx0 hxL (Ch.mem hik)⟩
  have hpos := Ch.run_pos (T := Ty.C2) (c := (n:ℝ) ^ 2) rfl hik.le hrun
  have hx : X (i + k) = X i + k * (n:ℝ) ^ 2 := hpos k le_rfl
  have hUT : ∀ j : ℕ, j < k → UT D n (-1) (X (i + k)) j 0 := by
    intro j hj
    have h := Ch.htile (i + (k - 1 - j)) (by omega)
    rw [hrun (k - 1 - j) (by omega)] at h
    have hcj : ((k - 1 - j : ℕ) : ℝ) = (k:ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hk1, Nat.cast_one]
    refine ⟨tile (i + (k - 1 - j)), S.c2_lp h ?_⟩
    rw [hpos (k - 1 - j) (by omega), hcj, hx]; ring
  refine C.run_dies hk1 hkn hUT ?_
  -- the first tile of the run, `U(k−1, 0)`
  have hτi : τ i = Ty.C2 := by
    have h := hrun 0 (by omega)
    rwa [Nat.add_zero] at h
  have hC2 := Ch.htile i (by omega)
  rw [hτi] at hC2
  have hU := S.c2_lp (x := X (i + k)) (ξ := (k:ℝ) - 1) hC2 (by rw [hx]; ring)
  have hG1 : 0 < (lp n (-1) (X (i + k)) ((k:ℝ) - 1) (0 + 1)) 1 := by rw [lp_one]; linarith
  have hA1 : (lp n (-1) (X (i + k)) ((k:ℝ) - 1) 0) 1 = 0 := by rw [lp_one]; ring
  have eV : lp n (-1) (X (i + k)) ((k:ℝ) - 1 + 1) 0 = mkPt (X i) 0 := by
    unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)
  have eA : lp n (-1) (X (i + k)) ((k:ℝ) - 1) 0 = mkPt (X i + (n:ℝ) ^ 2) 0 := by
    unfold lp; exact mkPt_congr (by rw [hx]; ring) (by ring)
  have hβ0 : (D.tile (tile i)).localAngle (mkPt (X i) 0) = β := (S.angles hC2).1
  have hU' := hU
  rw [eV] at hU'
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- the run starts at `Q`
    have hXi : X i = 0 := by rw [hi0]; exact Ch.hX0
    rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
    · exact S.K3_out_left ht hax hay (by rw [hx, hXi]; ring)
    · have hQ := S.corner_left_ab ht hax hay
      rw [hXi] at eV hβ0 hU'
      have eG : lp n (-1) (X (i + k)) ((k:ℝ) - 1) (0 + 1) = mkPt (uu n) (hh n) := by
        unfold lp; exact mkPt_congr (by rw [hx, hXi]; ring) (by ring)
      have hGmem : mkPt (uu (n:ℝ)) (hh n) ∈ D.target.carrier := by
        rw [← eG]; exact hU.mem₃
      have hQmem : mkPt 0 0 ∈ D.target.carrier := by
        have := Ch.mem (k := i) (by omega)
        rwa [hXi] at this
      have hint : openSegment ℝ (lp n (-1) (X (i + k)) ((k:ℝ) - 1 + 1) 0)
          (lp n (-1) (X (i + k)) ((k:ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
        rw [eV, eG]
        refine S.interior_seg hQmem hGmem (Or.inr (by rw [mkPt_one]; exact hhp)) (Or.inr ?_)
          (Or.inl ?_)
        · rw [gA_mk, hax, hay]
          have h1 := ruh hf1
          have e : t * rt n * uu n - t * hh n = t * rt n := by linear_combination t * h1
          rw [e]; exact mul_pos ht (rt_pos hf1.le)
        · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]
      refine C.K3_of_next hkn hU hint (fun W Z hW hθ hZ => ?_)
      rw [eV] at hW hθ
      exact S.bad_corner hQ hG1 hU' hA1 hβ0 hW hθ hZ
  · -- the tile before the run shows `γ`
    have hg : (τ (i - 1)).gR := by
      rcases hpred with h | h
      · omega
      · exact h
    have hxi0 : 0 < X i := Ch.pos S hipos (by omega)
    have hxiL : X i < L := Ch.lt_L S (by omega)
    have hp := Ch.htile (i - 1) (by omega)
    have e := Ch.prev hipos (by omega : i ≤ m)
    have hlenpos := Ty.lenR_pos S.f2 (τ (i - 1))
    have hγj : (D.tile (tile (i - 1))).localAngle (mkPt (X i) 0) = γ := by
      have h := (S.angles hp).2
      rw [e, Ty.aR_of_gR α β γ hg] at h
      exact h
    obtain ⟨kj, mj, jj, -, -, -, hkj, -, -, -⟩ := hp
    have hint : openSegment ℝ (lp n (-1) (X (i + k)) ((k:ℝ) - 1 + 1) 0)
        (lp n (-1) (X (i + k)) ((k:ℝ) - 1) (0 + 1)) ⊆ interior D.target.carrier := by
      rw [eV]
      refine S.interior_seg (Ch.mem (by omega)) hU.mem₃ (Or.inr hG1) (Or.inl ?_) (Or.inl ?_)
      · rw [gA_mk]; nlinarith [mul_pos S.hay hxi0]
      · rw [gB_mk]; nlinarith [mul_pos S.hay (sub_pos.mpr hxiL)]
    refine C.K3_of_next hkn hU hint (fun W Z hW hθ hZ => ?_)
    rw [eV] at hW hθ
    refine S.bad_nb hxi0 hxiL hG1 hU' hA1 hβ0 hkj (mkPt_one _ _)
      (mkPt_ne_of_fst (by linarith)) ?_ (Or.inl hγj) hW hθ hZ
    rw [eA]; exact mkPt_ne_of_fst (by linarith)

/-- **The typed word of the side satisfies the rules of the side theorem.** -/
theorem side_rules (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay)
    (Ch : Chain D n L m X tile τ) : SideRules n m τ := by
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ := S.alpha_lt_beta
  have hf1 := S.f1
  have hc := S.c_pos
  have hm0 := Ch.hm0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rQ
    have h := Ch.htile 0 hm0
    rw [Ch.hX0] at h
    have ha := (S.angles h).1
    have hle := one_angle_le D.toDissection (mkPt 0 0) (tile 0)
    have hQ := S.angleQ_le Co
    constructor
    · intro hT
      rw [hT] at ha
      have ha' : (D.tile (tile 0)).localAngle (mkPt 0 0) = γ := ha
      rw [ha'] at hle
      linarith
    · intro hT
      rw [hT] at ha
      have ha' : (D.tile (tile 0)).localAngle (mkPt 0 0) = γ := ha
      rw [ha'] at hle
      linarith
  · -- rB
    obtain ⟨hαβ', hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ', hγ0, hπ0⟩ := distinct_of_angleData S.hA
    obtain ⟨t, ht, hax, hay⟩ := Co.hB
    have h := Ch.htile (m - 1) (by omega)
    have hx := Ch.prev hm0 le_rfl
    rw [Ch.hXm] at hx
    have ha := (S.angles h).2
    rw [hx] at ha
    obtain ⟨k', m', j', -, -, -, -, hm', -, -⟩ := h
    rw [hx] at hm'
    have hmem : D.target.pts 1 ∈ (D.tile (tile (m - 1))).carrier := by
      rw [S.B_eq, ← hm']; exact subset_convexHull ℝ _ ⟨m', rfl⟩
    have hang := S.corner_tile_beta 1 (S.corner_right_beta ht hax hay) hmem
    rw [S.B_eq, ha] at hang
    exact Ty.aR_eq_beta hαβ' hβγ _ hang
  · -- rGG
    intro k hk hg hg'
    have h := Ch.htile k (by omega)
    have h' := Ch.htile (k + 1) hk
    have hs := Ch.hstep k (by omega)
    have hl := Ty.lenR_pos S.f2 (τ k)
    have hij : tile k ≠ tile (k + 1) := S.baseTile_ne h h' (by rw [hs]; linarith)
    have h1 := (S.angles h).2
    have h2 := (S.angles h').1
    rw [← hs, Ty.aR_of_gR α β γ hg] at h1
    rw [Ty.aL_of_gL α β γ hg'] at h2
    have h3 := two_angles_le D.toDissection (mkPt (X (k + 1)) 0) hij
    rw [h1, h2, S.angle_base (Ch.pos S (by omega) (by omega)) (Ch.lt_L S hk)] at h3
    linarith
  · -- ra
    intro i k hk1 hkn hik hrun hp
    by_contra hcon
    have hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1) := by
      rcases Nat.lt_or_ge (i + k) m with h | h
      · exact Or.inr ⟨h, fun hB => hcon ⟨h, Or.inl hB⟩, fun hC => hcon ⟨h, Or.inr hC⟩⟩
      · exact Or.inl (by omega)
    have hτi : τ i = Ty.C1 := by
      have h := hrun 0 (by omega)
      rwa [Nat.add_zero] at h
    have h00 := Ch.htile i (by omega)
    rw [hτi] at h00
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · have hXi : X i = 0 := by rw [hi0]; exact Ch.hX0
      have hQmem : mkPt 0 0 ∈ D.target.carrier := by
        have := Ch.mem (k := i) (by omega)
        rwa [hXi] at this
      rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
      · -- a corner of angle `β`: its tile shows `β`, not `α`
        have ha := (S.angles h00).1
        rw [hXi] at ha
        obtain ⟨k', m', j', -, -, -, hk', -, -, -⟩ := h00
        rw [hXi] at hk'
        have hmem : D.target.pts 0 ∈ (D.tile (tile i)).carrier := by
          rw [S.Q_eq, ← hk']; exact subset_convexHull ℝ _ ⟨k', rfl⟩
        have hang := S.corner_tile_beta 0 (S.corner_left_beta ht hax hay) hmem
        rw [S.Q_eq, ha] at hang
        have hang' : α = β := hang
        linarith
      · have hQ := S.corner_left_ab ht hax hay
        have hU0 := S.c1_lp (x := (0:ℝ)) (ξ := 0) h00 (by rw [hXi]; ring)
        exact S.kill_C1 Co Ch hk1 hkn hik hrun hXi (S.K1_of_corner (by norm_num) hQ hU0)
          (S.hch_corner ht hax hay hQmem) hsucc
    · have hg : (τ (i - 1)).gR := by
        rcases hp with h | h
        · omega
        · exact h
      have hx0 : 0 < X i := Ch.pos S hipos (by omega)
      have hxL : X i < L := Ch.lt_L S (by omega)
      have hU0 := S.c1_lp (x := X i) (ξ := 0) h00 (by ring)
      have hpj := Ch.htile (i - 1) (by omega)
      have e := Ch.prev hipos (by omega : i ≤ m)
      have hγj : (D.tile (tile (i - 1))).localAngle (mkPt (X i) 0) = γ := by
        have h := (S.angles hpj).2
        rw [e, Ty.aR_of_gR α β γ hg] at h
        exact h
      have hlam : (τ (i - 1)).lenR (n:ℝ) = n ∨ (τ (i - 1)).lenR (n:ℝ) = (n:ℝ) ^ 2 - 1 := by
        rcases hg with h | h
        · rw [h]; exact Or.inl rfl
        · rw [h]; exact Or.inr rfl
      obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hpj
      rw [e] at hmj
      have hkj' : (D.tile (tile (i - 1))).pts kj = mkPt (X i - 1 * (τ (i - 1)).lenR (n:ℝ)) 0 := by
        rw [hkj]; exact mkPt_congr (by rw [← e]; ring) rfl
      exact S.kill_C1 Co Ch hk1 hkn hik hrun rfl
        (S.K1_of_gamma (by norm_num) hx0 hxL hU0 (Ne.symm hkmj) hmj hkj' hlam hγj)
        (S.hch_pos hx0 hxL (Ch.mem (by omega))) hsucc
  · -- rb
    intro i k hk1 hkn hik hrun hp hgL
    have hx0 : 0 < X (i + k) := Ch.pos S (by omega) (by omega)
    have hxL : X (i + k) < L := Ch.lt_L S hik
    have hlast := Ch.htile (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega)] at hlast
    have hstep := Ch.hstep (i + (k - 1)) (by omega)
    rw [hrun (k - 1) (by omega), show i + (k - 1) + 1 = i + k by omega] at hstep
    have hU0 := S.c2_lp (x := X (i + k)) (ξ := 0) hlast (by
      have h' : X (i + k) = X (i + (k - 1)) + (n:ℝ) ^ 2 := hstep
      rw [h']; ring)
    have hj := Ch.htile (i + k) hik
    have hγj : (D.tile (tile (i + k))).localAngle (mkPt (X (i + k)) 0) = γ := by
      have h := (S.angles hj).1
      rw [Ty.aL_of_gL α β γ hgL] at h
      exact h
    have hlam : (τ (i + k)).lenR (n:ℝ) = n ∨ (τ (i + k)).lenR (n:ℝ) = (n:ℝ) ^ 2 - 1 := by
      rcases hgL with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl
    obtain ⟨kj, mj, jj, hkmj, -, -, hkj, hmj, -, -⟩ := hj
    have hmj' : (D.tile (tile (i + k))).pts mj
        = mkPt (X (i + k) - (-1) * (τ (i + k)).lenR (n:ℝ)) 0 := by
      rw [hmj]; exact mkPt_congr (by ring) rfl
    exact S.kill_C2 Co Ch hk1 hkn hik hrun
      (S.K1_of_gamma (by norm_num) hx0 hxL hU0 hkmj hkj hmj' hlam hγj) hp
  · -- rc
    intro i s r hs1 hsn hr1 hrn hisr hrun2 hrun1 hp
    have hJ0 : 0 < X (i + s) := Ch.pos S (by omega) (by omega)
    have hJL : X (i + s) < L := Ch.lt_L S (by omega)
    -- the first `C1` and the last `C2`
    have hτ1 : τ (i + s) = Ty.C1 := by
      have h := hrun1 0 (by omega)
      rwa [Nat.add_zero] at h
    have h1 := Ch.htile (i + s) (by omega)
    rw [hτ1] at h1
    have hU1 := S.c1_lp (x := X (i + s)) (ξ := 0) h1 (by ring)
    have hlast := Ch.htile (i + (s - 1)) (by omega)
    rw [hrun2 (s - 1) (by omega)] at hlast
    have hstep := Ch.hstep (i + (s - 1)) (by omega)
    rw [hrun2 (s - 1) (by omega), show i + (s - 1) + 1 = i + s by omega] at hstep
    have hU2 := S.c2_lp (x := X (i + s)) (ξ := 0) hlast (by
      have h' : X (i + s) = X (i + (s - 1)) + (n:ℝ) ^ 2 := hstep
      rw [h']; ring)
    rcases S.junction hJ0 hJL hU1 hU2 with hK | hK
    · by_contra hcon
      have hsucc : i + s + r = m ∨
          (i + s + r < m ∧ τ (i + s + r) ≠ Ty.B1 ∧ τ (i + s + r) ≠ Ty.C1) := by
        rcases Nat.lt_or_ge (i + s + r) m with h | h
        · exact Or.inr ⟨h, fun hB => hcon ⟨h, Or.inl hB⟩, fun hC => hcon ⟨h, Or.inr hC⟩⟩
        · exact Or.inl (by omega)
      exact S.kill_C1 Co Ch hr1 hrn hisr hrun1 rfl hK
        (S.hch_pos hJ0 hJL (Ch.mem (by omega))) hsucc
    · exact (S.kill_C2 Co Ch hs1 hsn (by omega) hrun2 hK hp).elim

/-- **THE SIDE THEOREM** (both forms).  In a dissection of the triangle `Q = (0,0)`, `B = (L,0)`, `A` into copies
of the tile `(n, n²−1, n²)`, `n ≥ 2`, where the corner `B` has angle `β` and the corner `Q` has angle `β` (first
form) or `α + β` (second form), the side `QB` carries `n` consecutive tiles of type `C1` or `n` consecutive tiles
of type `C2`. -/
theorem side_theorem (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay)
    (Ch : Chain D n L m X tile τ) :
    ∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = Ty.C1) ∨ (∀ j, j < n → τ (i + j) = Ty.C2)) :=
  side_word n m τ Ch.hm0 (S.side_rules Co Ch)

/-- the side theorem, with the chain of the dissection -/
theorem side_theorem' (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay) :
    ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), Chain D n L m X tile τ ∧
      ∃ i, i + n ≤ m ∧ ((∀ j, j < n → τ (i + j) = Ty.C1) ∨ (∀ j, j < n → τ (i + j) = Ty.C2)) := by
  obtain ⟨m, X, tile, τ, hm0, hX0, hXm, hstep, htile⟩ := S.typed_chain
  have Ch : Chain D n L m X tile τ := ⟨hm0, hX0, hXm, hstep, htile⟩
  exact ⟨m, X, tile, τ, Ch, S.side_theorem Co Ch⟩

/-- **No dissection** when the side `QB` has the length `M (κ n² − 1)` with `(κ − 1) M < n`: it would carry at
least `n` tiles with `c` on it and at least `M` with `b`. -/
theorem no_tiling_of_length (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay) {M κ : ℕ}
    (hκ : 2 ≤ κ) (hκM : (κ - 1) * M < n) (hL : L = (M:ℝ) * (κ * (n:ℝ) ^ 2 - 1)) : False := by
  obtain ⟨m, X, tile, τ, hm0, hX0, hXm, hstep, htile⟩ := S.typed_chain
  have Ch : Chain D n L m X tile τ := ⟨hm0, hX0, hXm, hstep, htile⟩
  have hn1 : 1 ≤ n := by have := S.hn2; omega
  refine no_side_word S.hn2 hκ hκM hm0 τ ?_ (S.side_rules Co Ch)
  rw [Nat.cast_sum, Finset.sum_congr rfl (fun k _ => Ty.len_cast n hn1 (τ k))]
  have h2 : ∀ k ∈ Finset.range m, (τ k).lenR n = X (k + 1) - X k := by
    intro k hk
    rw [hstep k (Finset.mem_range.mp hk)]; ring
  rw [Finset.sum_congr rfl h2, Finset.sum_range_sub, hXm, hX0, sub_zero, hL]

end Setup

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.Setup.kill_C1
#print axioms Erdos634.Draft.SideRun.Setup.kill_C2
#print axioms Erdos634.Draft.SideRun.Setup.side_rules
#print axioms Erdos634.Draft.SideRun.Setup.side_theorem
#print axioms Erdos634.Draft.SideRun.Setup.no_tiling_of_length
