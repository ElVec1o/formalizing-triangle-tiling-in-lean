/-
Draft/SideRunGSourcesC.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module 8 of ten
(part C: the checks at `e = 1` of parts A and B).

Each source of `Draft/SideRunGSources.lean` and the run lemma of `Draft/SideRunGSourcesB.lean`, taken at `e = 1`, gives the
statement of `Draft/SideRunSources.lean` / `Draft/SideRunRules.lean`:
* the figures `gamma_alpha_alpha`, `four_alpha`, `three_beta`, `corner_two_alpha`: the e = 1 statements ARE the general ones
  (they mention only `mkPt` points and angles): `…_e1`;
* the chords `hch_pos_e1`, `hch_corner_e1`; (K1): `K1_of_gamma_e1`, `K1_of_corner_e1`, `junction_e1`;
* (K3): `K3_out_right_e1`, `K3_out_left_e1` (through the first-alternative statements `out_right`, `out_left`),
  `bad_nb_e1`, `bad_corner_e1` (the e = 1 proofs use `α < β`; the general ones do not, so these re-derivations also give the
  e = 1 statements without any order of `α, β`), `K3_of_next_e1` (through `K3_of_K3G_e1`, which needs `k + 1 ≤ n`, true
  for a run of `k < n` tiles);
* the structures: `cornersG_of`, `chainG_of` (`Corners n L ax ay` gives `CornersG 1 n L ax ay`; `Chain` gives `ChainG`);
* the run lemma: `kill_C1_e1`, `kill_C2_e1` are the statements of `SideRun.Setup.kill_C1`, `kill_C2`, derived from `kill_C1G`,
  `kill_C2G`.  (Unlike `K_all`, they DO reduce: the hypotheses of the e = 1 run lemma and of the general one agree, and the
  conclusion is `False`.)

WHAT DOES NOT REDUCE.  Nothing in this list fails to reduce.  The converse direction (the general statement from the e = 1 one)
is not claimed for `K3_of_next` and `K3_out_*`: the general ones end in `K3G`, which at `e = 1` implies `K3` (with `k + 1 ≤ n`)
but not conversely.  The polynomial argument inside `K1_of_gamma` (`uuG ≠ e f`) is, at `e = 1`, `uu n ≠ n`, i.e. `2 n³ − 3 n² + 1 = (n − 1)² (2 n + 1) ≠ 0`.

WITNESSES.  As in parts A and B: `SetupG`, `CtxG`, `CornersG`, `ChainG` are satisfied at `e = 1` exactly by `Setup`, `Ctx`
(`setupG_one_iff`, `ctxG_one_iff`), `Corners`, `Chain` (`cornersG_of`, `chainG_of`; the converses are not needed); NO object
for `e ≥ 2` exists yet.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGSourcesB
import Erdos634.Draft.SideRunRules

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay ε x : ℝ}

/-! ## 1. Figures -/

theorem gamma_alpha_alpha_e1 (S : Setup D n α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i j l : Fin N} (hil : i ≠ l) (hi : (D.tile i).localAngle (mkPt v 0) = α)
    (hj : (D.tile j).localAngle (mkPt v 0) = γ) (hl : (D.tile l).localAngle (mkPt v 0) = α) :
    False :=
  (setupG_one_iff.mpr S).gamma_alpha_alpha hv0 hvL hil hi hj hl

theorem four_alpha_e1 (S : Setup D n α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i k₁ k₂ l : Fin N} (h12 : i ≠ k₁) (h13 : i ≠ k₂) (h14 : i ≠ l) (h23 : k₁ ≠ k₂)
    (h24 : k₁ ≠ l) (h34 : k₂ ≠ l) (hi : (D.tile i).localAngle (mkPt v 0) = α)
    (hk₁ : (D.tile k₁).localAngle (mkPt v 0) = α) (hk₂ : (D.tile k₂).localAngle (mkPt v 0) = α)
    (hl : (D.tile l).localAngle (mkPt v 0) = α) : False :=
  (setupG_one_iff.mpr S).four_alpha hv0 hvL h12 h13 h14 h23 h24 h34 hi hk₁ hk₂ hl

theorem three_beta_e1 (S : Setup D n α β γ L ax ay) {v : ℝ} (hv0 : 0 < v) (hvL : v < L)
    {i j l : Fin N} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hi : (D.tile i).localAngle (mkPt v 0) = β) (hj : (D.tile j).localAngle (mkPt v 0) = β)
    (hl : (D.tile l).localAngle (mkPt v 0) = β) : False :=
  (setupG_one_iff.mpr S).three_beta hv0 hvL hij hil hjl hi hj hl

theorem corner_two_alpha_e1 (S : Setup D n α β γ L ax ay)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {i j : Fin N} (hij : i ≠ j)
    (hi : (D.tile i).localAngle (mkPt 0 0) = α) (hj : (D.tile j).localAngle (mkPt 0 0) = α) :
    False :=
  (setupG_one_iff.mpr S).corner_two_alpha hQ hij hi hj

/-! ## 2. The chords and (K1) -/

theorem hch_pos_e1 (S : Setup D n α β γ L ax ay) (hx0 : 0 < x) (hxL : x < L)
    (hP : mkPt x 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lp n ε x 0 j ∈ D.target.carrier →
      openSegment ℝ (lp n ε x 0 0) (lp n ε x 0 j) ⊆ interior D.target.carrier := by
  intro j hj hmem
  have h := (setupG_one_iff.mpr S).hch_pos (ε := ε) hx0 hxL hP j hj
    (by rw [Nat.cast_one, lpG_one]; exact hmem)
  simpa only [Nat.cast_one, lpG_one] using h

theorem hch_corner_e1 (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t) (hax : ax = t)
    (hay' : ay = t * rt n) (hP : mkPt 0 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lp n 1 0 0 j ∈ D.target.carrier →
      openSegment ℝ (lp n 1 0 0 0) (lp n 1 0 0 j) ⊆ interior D.target.carrier := by
  intro j hj hmem
  have h := (setupG_one_iff.mpr S).hch_corner ht (by rw [Nat.cast_one, mul_one]; exact hax)
    (by rw [Nat.cast_one, rtG_one]; exact hay') hP j hj (by rw [Nat.cast_one, lpG_one]; exact hmem)
  simpa only [Nat.cast_one, lpG_one] using h

theorem K1_of_gamma_e1 (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1) (hx0 : 0 < x) (hxL : x < L)
    {t₀ : Fin N}
    (h0 : HasV D t₀ (lp n ε x 0 0) (lp n ε x (0 + 1) 0) (lp n ε x 0 (0 + 1)))
    {j : Fin N} {kj mj : Fin 3} {lam : ℝ} (hkmj : kj ≠ mj) (hkj : (D.tile j).pts kj = mkPt x 0)
    (hmj : (D.tile j).pts mj = mkPt (x - ε * lam) 0) (hlam : lam = n ∨ lam = (n : ℝ) ^ 2 - 1)
    (hγj : (D.tile j).localAngle (mkPt x 0) = γ) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n ε x 0 0 →
      (D.tile t').pts m = lp n ε x 0 1 → (∀ i, FX n ε ((D.tile t').pts i) ≤ lv n ε x 0) → False := by
  intro t' k m hkm hk hm hle
  refine (setupG_one_iff.mpr S).K1_of_gamma hε hx0 hxL (by simpa only [Nat.cast_one, lpG_one] using h0)
    hkmj hkj hmj ?_ hγj t' k m hkm (by rw [Nat.cast_one, lpG_one]; exact hk)
    (by rw [Nat.cast_one, lpG_one]; exact hm) (fun i => by
      simpa only [Nat.cast_one, FXG_one, lvG_one] using hle i)
  rcases hlam with h | h
  · left; rw [h, Nat.cast_one, one_mul]
  · right; rw [h, Nat.cast_one, one_pow]

theorem K1_of_corner_e1 (S : Setup D n α β γ L ax ay) (hε : ε ^ 2 = 1)
    (hQ : D.target.localAngle (mkPt 0 0) = α + β) {t₀ : Fin N}
    (h0 : HasV D t₀ (lp n ε 0 0 0) (lp n ε 0 (0 + 1) 0) (lp n ε 0 0 (0 + 1))) :
    ∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n ε 0 0 0 →
      (D.tile t').pts m = lp n ε 0 0 1 → (∀ i, FX n ε ((D.tile t').pts i) ≤ lv n ε 0 0) → False := by
  intro t' k m hkm hk hm hle
  exact (setupG_one_iff.mpr S).K1_of_corner hε hQ (by simpa only [Nat.cast_one, lpG_one] using h0)
    t' k m hkm (by rw [Nat.cast_one, lpG_one]; exact hk) (by rw [Nat.cast_one, lpG_one]; exact hm)
    (fun i => by simpa only [Nat.cast_one, FXG_one, lvG_one] using hle i)

theorem junction_e1 (S : Setup D n α β γ L ax ay) (hx0 : 0 < x) (hxL : x < L) {t₁ t₂ : Fin N}
    (h1 : HasV D t₁ (lp n 1 x 0 0) (lp n 1 x (0 + 1) 0) (lp n 1 x 0 (0 + 1)))
    (h2 : HasV D t₂ (lp n (-1) x 0 0) (lp n (-1) x (0 + 1) 0) (lp n (-1) x 0 (0 + 1))) :
    (∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n 1 x 0 0 →
      (D.tile t').pts m = lp n 1 x 0 1 → (∀ i, FX n 1 ((D.tile t').pts i) ≤ lv n 1 x 0) → False) ∨
    (∀ (t' : Fin N) (k m : Fin 3), k ≠ m → (D.tile t').pts k = lp n (-1) x 0 0 →
      (D.tile t').pts m = lp n (-1) x 0 1 → (∀ i, FX n (-1) ((D.tile t').pts i) ≤ lv n (-1) x 0) →
      False) := by
  rcases (setupG_one_iff.mpr S).junction hx0 hxL (by simpa only [Nat.cast_one, lpG_one] using h1)
    (by simpa only [Nat.cast_one, lpG_one] using h2) with hA | hA
  · left
    intro t' k m hkm hk hm hle
    exact hA t' k m hkm (by rw [Nat.cast_one, lpG_one]; exact hk)
      (by rw [Nat.cast_one, lpG_one]; exact hm)
      (fun i => by simpa only [Nat.cast_one, FXG_one, lvG_one] using hle i)
  · right
    intro t' k m hkm hk hm hle
    exact hA t' k m hkm (by rw [Nat.cast_one, lpG_one]; exact hk)
      (by rw [Nat.cast_one, lpG_one]; exact hm)
      (fun i => by simpa only [Nat.cast_one, FXG_one, lvG_one] using hle i)

/-! ## 3. (K3) -/

theorem K3_out_right_e1 (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * uu n) (hay' : ay = t * hh n) {k : ℝ} (hx : x + k * (n : ℝ) ^ 2 = L) :
    K3 D n 1 x k 0 :=
  K3_of_outG ((setupG_one_iff.mpr S).out_right ht (by rw [Nat.cast_one, uuG_one]; exact hax)
    (by rw [Nat.cast_one, hhG_one]; exact hay') hx)

theorem K3_out_left_e1 (S : Setup D n α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * uu n) (hay' : ay = t * hh n) {k : ℝ} (hx : x - k * (n : ℝ) ^ 2 = 0) :
    K3 D n (-1) x k 0 :=
  K3_of_outG ((setupG_one_iff.mpr S).out_left ht (by rw [Nat.cast_one, uuG_one]; exact hax)
    (by rw [Nat.cast_one, hhG_one]; exact hay') hx)

theorem bad_nb_e1 (S : Setup D n α β γ L ax ay) {xR : ℝ} (hx0 : 0 < xR) (hxL : xR < L)
    {G A₀ Rp Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N} (h0 : HasV D t₀ A₀ (mkPt xR 0) G)
    (hA₀ : A₀ 1 = 0) (hβ0 : (D.tile t₀).localAngle (mkPt xR 0) = β)
    {j : Fin N} {mj : Fin 3} (hmj : (D.tile j).pts mj = Rp) (hRp1 : Rp 1 = 0)
    (hRpV : Rp ≠ mkPt xR 0) (hRpA : Rp ≠ A₀)
    (hθj : (D.tile j).localAngle (mkPt xR 0) = γ ∨ (D.tile j).localAngle (mkPt xR 0) = β)
    {W : Fin N} (hW : HasV D W (mkPt xR 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt xR 0) = γ ∨ (D.tile W).localAngle (mkPt xR 0) = β)
    (hZ1 : 0 < Z 1) : False :=
  (setupG_one_iff.mpr S).bad_nb hx0 hxL hG1 h0 hA₀ hβ0 hmj hRp1 hRpV hRpA hθj hW hθW hZ1

theorem bad_corner_e1 (S : Setup D n α β γ L ax ay) (hQ : D.target.localAngle (mkPt 0 0) = α + β)
    {G A₀ Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N} (h0 : HasV D t₀ A₀ (mkPt 0 0) G)
    (hA₀ : A₀ 1 = 0) (hβ0 : (D.tile t₀).localAngle (mkPt 0 0) = β)
    {W : Fin N} (hW : HasV D W (mkPt 0 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt 0 0) = γ ∨ (D.tile W).localAngle (mkPt 0 0) = β)
    (hZ1 : 0 < Z 1) : False :=
  (setupG_one_iff.mpr S).bad_corner hQ hG1 h0 hA₀ hβ0 hW hθW hZ1

theorem K3_of_next_e1 (C : Ctx D n α β γ L ax ay ε x) {k : ℕ} (hkn : k < n) {t₀ : Fin N}
    (hU : HasV D t₀ (lp n ε x ((k : ℝ) - 1) 0) (lp n ε x ((k : ℝ) - 1 + 1) 0)
      (lp n ε x ((k : ℝ) - 1) (0 + 1)))
    (hint : openSegment ℝ (lp n ε x ((k : ℝ) - 1 + 1) 0) (lp n ε x ((k : ℝ) - 1) (0 + 1))
      ⊆ interior D.target.carrier)
    (hbad : ∀ (W : Fin N) (Z : Plane),
      HasV D W (lp n ε x ((k : ℝ) - 1 + 1) 0) (lp n ε x ((k : ℝ) - 1) (0 + 1)) Z →
      ((D.tile W).localAngle (lp n ε x ((k : ℝ) - 1 + 1) 0) = γ ∨
        (D.tile W).localAngle (lp n ε x ((k : ℝ) - 1 + 1) 0) = β) → 0 < Z 1 → False) :
    K3 D n ε x k 0 := by
  have CG := ctxG_one_iff.mpr C
  have hn : 2 ≤ n := C.S.hn2
  have hs : (k : ℝ) + 1 ≤ (n : ℝ) := by
    have h' : k + 1 ≤ n := hkn
    exact_mod_cast h'
  refine K3_of_K3G_e1 hn hs (CG.K3G_of_next (by simpa only [Nat.cast_one, lpG_one] using hU)
    (by simpa only [Nat.cast_one, lpG_one] using hint) (fun W Z hW hθ hZ => ?_))
  exact hbad W Z (by simpa only [Nat.cast_one, lpG_one] using hW)
    (by simpa only [Nat.cast_one, lpG_one] using hθ) hZ

/-! ## 4. The run lemma `L_k` -/

theorem cornersG_of (Co : Corners n L ax ay) : CornersG 1 n L ax ay := by
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht, hax, hay⟩ := Co.hB
    exact ⟨t, ht, by rw [Nat.cast_one, uuG_one]; exact hax, by rw [Nat.cast_one, hhG_one]; exact hay⟩
  · rcases Co.hQ with ⟨t, ht, hax, hay⟩ | ⟨t, ht, hax, hay⟩
    · exact Or.inl ⟨t, ht, by rw [Nat.cast_one, uuG_one]; exact hax,
        by rw [Nat.cast_one, hhG_one]; exact hay⟩
    · exact Or.inr ⟨t, ht, by rw [Nat.cast_one, mul_one]; exact hax,
        by rw [Nat.cast_one, rtG_one]; exact hay⟩

theorem chainG_of {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N} {τ : ℕ → Ty}
    (Ch : Chain D n L m X tile τ) : ChainG D 1 n L m X tile τ := by
  refine ⟨Ch.hm0, Ch.hX0, Ch.hXm, fun k hk => ?_, fun k hk => ?_⟩
  · have h := Ch.hstep k hk
    rw [Nat.cast_one, Ty.lenG_one]; exact h
  · obtain ⟨k₁, m₁, j₁, h1, h2, h3, h4, h5, h6, h7⟩ := Ch.htile k hk
    refine ⟨k₁, m₁, j₁, h1, h2, h3, h4, ?_, ?_, ?_⟩
    · rw [Nat.cast_one, Ty.lenG_one]; exact h5
    · rw [Nat.cast_one, Ty.sLG_one]; exact h6
    · rw [Nat.cast_one, Ty.sRG_one]; exact h7

/-- **`SetupG.kill_C1G` at `e = 1` is `SideRun.Setup.kill_C1`** -/
theorem kill_C1_e1 (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay) {m : ℕ} {X : ℕ → ℝ}
    {tile : ℕ → Fin N} {τ : ℕ → Ty} (Ch : Chain D n L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (hik : i + k ≤ m) (hrun : ∀ j, j < k → τ (i + j) = Ty.C1) {x : ℝ} (hxi : X i = x)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lp n 1 x 0 0 →
      (D.tile t').pts m' = lp n 1 x 0 1 → (∀ i', FX n 1 ((D.tile t').pts i') ≤ lv n 1 x 0) → False)
    (hch : ∀ j : ℕ, 1 ≤ j → lp n 1 x 0 j ∈ D.target.carrier →
      openSegment ℝ (lp n 1 x 0 0) (lp n 1 x 0 j) ⊆ interior D.target.carrier)
    (hsucc : i + k = m ∨ (i + k < m ∧ τ (i + k) ≠ Ty.B1 ∧ τ (i + k) ≠ Ty.C1)) : False :=
  (setupG_one_iff.mpr S).kill_C1G (cornersG_of Co) (chainG_of Ch) hk1 hkn hik hrun hxi
    (fun t' k' m' hkm hk hm hle => hK1 t' k' m' hkm (by rwa [Nat.cast_one, lpG_one] at hk)
      (by rwa [Nat.cast_one, lpG_one] at hm)
      (fun i' => by simpa only [Nat.cast_one, FXG_one, lvG_one] using hle i'))
    (fun j hj hmem => by
      have h := hch j hj (by simpa only [Nat.cast_one, lpG_one] using hmem)
      simpa only [Nat.cast_one, lpG_one] using h)
    hsucc

/-- **`SetupG.kill_C2G` at `e = 1` is `SideRun.Setup.kill_C2`** -/
theorem kill_C2_e1 (S : Setup D n α β γ L ax ay) (Co : Corners n L ax ay) {m : ℕ} {X : ℕ → ℝ}
    {tile : ℕ → Fin N} {τ : ℕ → Ty} (Ch : Chain D n L m X tile τ) {i k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (hik : i + k < m) (hrun : ∀ j, j < k → τ (i + j) = Ty.C2)
    (hK1 : ∀ (t' : Fin N) (k' m' : Fin 3), k' ≠ m' → (D.tile t').pts k' = lp n (-1) (X (i + k)) 0 0 →
      (D.tile t').pts m' = lp n (-1) (X (i + k)) 0 1 →
      (∀ i', FX n (-1) ((D.tile t').pts i') ≤ lv n (-1) (X (i + k)) 0) → False)
    (hpred : i = 0 ∨ (τ (i - 1)).gR) : False :=
  (setupG_one_iff.mpr S).kill_C2G (cornersG_of Co) (chainG_of Ch) hk1 hkn hik hrun
    (fun t' k' m' hkm hk hm hle => hK1 t' k' m' hkm (by rwa [Nat.cast_one, lpG_one] at hk)
      (by rwa [Nat.cast_one, lpG_one] at hm)
      (fun i' => by simpa only [Nat.cast_one, FXG_one, lvG_one] using hle i'))
    hpred

end Erdos634.Draft.SideRunG

#print axioms Erdos634.Draft.SideRunG.hch_pos_e1
#print axioms Erdos634.Draft.SideRunG.hch_corner_e1
#print axioms Erdos634.Draft.SideRunG.K1_of_gamma_e1
#print axioms Erdos634.Draft.SideRunG.K1_of_corner_e1
#print axioms Erdos634.Draft.SideRunG.junction_e1
#print axioms Erdos634.Draft.SideRunG.K3_out_right_e1
#print axioms Erdos634.Draft.SideRunG.K3_out_left_e1
#print axioms Erdos634.Draft.SideRunG.bad_nb_e1
#print axioms Erdos634.Draft.SideRunG.bad_corner_e1
#print axioms Erdos634.Draft.SideRunG.K3_of_next_e1
#print axioms Erdos634.Draft.SideRunG.kill_C1_e1
#print axioms Erdos634.Draft.SideRunG.kill_C2_e1
