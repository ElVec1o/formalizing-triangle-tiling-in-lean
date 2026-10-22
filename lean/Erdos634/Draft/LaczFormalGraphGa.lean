-- Draft/LaczFormalGraphGa.lean -- D2 (part 1): maximal segments, side lengths and the A-RUN of a division.
-- `side_len_mem`: every step of a walk is a side of a tile, so its length is `a`, `b` or `c` (`slen D 0/1/2`).  `exists_maxwalk(T/R)`: maximal walks exist.
-- `exists_maxseg`: from a vertex `X` with a left tile and a right tile starting along `d`, the two maximal walks end at the same point `Y`
-- (`ends_coincide`).  `arun_end`: if the first left side has length `a`, the first right side does not, and `a` is not a nonnegative rational combination of
-- `b, c` (`NotComb`), then some left side is not `a`: the index `i_0` of Laczkovich's definition of `Γ_a` exists.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4: definition of Gamma_a: "there is a unique index 1 <= i_0 < k"); Beeson (1206.2229, Def. 4).
import Erdos634.Draft.LaczFormalGraphEnds

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- `a` is not a positive rational multiple... precisely: `r * a ≠ p * b + q * c` for all naturals `r > 0, p, q`. -/
def NotComb (a b c : ℝ) : Prop := ∀ r p q : ℕ, 0 < r → (r : ℝ) * a ≠ p * b + q * c

/-- A step is a side of its tile: its length is one of the model sides. -/
theorem side_len_mem (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {i : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile i) d U U') :
    dist U U' = slen D 0 ∨ dist U U' = slen D 1 ∨ dist U U' = slen D 2 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, -⟩ := hS
  rw [← hk, ← hf]
  rcases fin3_arm kk f hfk with h | h
  · subst h
    rw [side_len_01 D idx hidx]
    generalize idx i (kk + 2) = t
    fin_cases t <;> simp
  · subst h
    rw [side_len_02 D idx hidx]
    generalize idx i (kk + 1) = t
    fin_cases t <;> simp

/-- The finite set of tile vertices. -/
noncomputable def vtxSet (D : Dissection N) : Finset Plane :=
  (Finset.univ : Finset (Fin N × Fin 3)).image (fun p => (D.tile p.1).pts p.2)

theorem mem_vtxSet {D : Dissection N} {U : Plane} : U ∈ vtxSet D ↔ ∃ j k, (D.tile j).pts k = U := by
  unfold vtxSet
  constructor
  · intro h
    obtain ⟨⟨j, k⟩, -, hjk⟩ := Finset.mem_image.mp h
    exact ⟨j, k, hjk⟩
  · rintro ⟨j, k, h⟩
    exact Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, h⟩

/-- **Maximal left walks exist.** -/
theorem exists_maxwalkT (D : Dissection N) {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X) :
    ∃ Y L, WalkT D d X Y L ∧ ∀ i U', ¬ TriStep (D.tile i) d Y U' := by
  classical
  have hnd : 0 < nsq d := nsq_pos hd
  set F : Plane → Finset Plane := fun U => (vtxSet D).filter (fun v => dt d (toV2 (v - X)) > dt d (toV2 (U - X))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      ∃ Y L, WalkT D d U Y L ∧ ∀ i U', ¬ TriStep (D.tile i) d Y U' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert
      by_cases hstep : ∃ i U', TriStep (D.tile i) d U U'
      · obtain ⟨i, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hdec : toV2 (U' - X) = ((toV2 (U' - U)).1 + (toV2 (U - X)).1, (toV2 (U' - U)).2 + (toV2 (U - X)).2) := by
          unfold toV2; ext <;> simp
        have hdt : dt d (toV2 (U' - X)) > dt d (toV2 (U - X)) := by
          rw [hdec, hcw]
          unfold dt nsq at *; try simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨i, f, hf⟩
        have hsub : F U' ⊂ F U := by
          refine ⟨?_, ?_⟩
          · intro v hv
            simp only [hF, Finset.mem_filter] at hv ⊢
            exact ⟨hv.1, lt_trans hdt hv.2⟩
          · intro hsub
            have hU'mem : U' ∈ F U := by
              simp only [hF, Finset.mem_filter]
              exact ⟨mem_vtxSet.mpr hvert', hdt⟩
            have := hsub hU'mem
            simp only [hF, Finset.mem_filter] at this
            exact lt_irrefl _ this.2
        have hlt : (F U').card < n := hcard ▸ Finset.card_lt_card hsub
        obtain ⟨Y, L, hW, hY⟩ := ih (F U').card hlt U' rfl hvert'
        exact ⟨Y, (i, U, U') :: L, WalkT.cons hS hW, hY⟩
      · push_neg at hstep
        exact ⟨U, [], WalkT.nil U, hstep⟩
  exact key _ X rfl hX

/-- **Maximal right walks exist.** -/
theorem exists_maxwalkR (D : Dissection N) {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X) :
    ∃ Y L, WalkR D d X Y L ∧ ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y := by
  classical
  have hnd : 0 < nsq d := nsq_pos hd
  set F : Plane → Finset Plane := fun U => (vtxSet D).filter (fun v => dt d (toV2 (v - X)) > dt d (toV2 (U - X))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      ∃ Y L, WalkR D d U Y L ∧ ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert
      by_cases hstep : ∃ i U', TriStep (D.tile i) (neg2 d) U' U
      · obtain ⟨i, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        -- hk : pts kk = U', hf : pts f = U ; hpar : Par (toV2 (U - U')) (neg2 d)
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hUU' : toV2 (U' - U) = (c * d.1, c * d.2) := by
          have : toV2 (U' - U) = (-(toV2 (U - U')).1, -(toV2 (U - U')).2) := by
            unfold toV2; ext <;> simp
          rw [this, hcw]; unfold neg2; ext <;> simp
        have hdec : toV2 (U' - X) = ((toV2 (U' - U)).1 + (toV2 (U - X)).1, (toV2 (U' - U)).2 + (toV2 (U - X)).2) := by
          unfold toV2; ext <;> simp
        have hdt : dt d (toV2 (U' - X)) > dt d (toV2 (U - X)) := by
          rw [hdec, hUU']
          unfold dt nsq at *; try simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨i, kk, hk⟩
        have hsub : F U' ⊂ F U := by
          refine ⟨?_, ?_⟩
          · intro v hv
            simp only [hF, Finset.mem_filter] at hv ⊢
            exact ⟨hv.1, lt_trans hdt hv.2⟩
          · intro hsub
            have hU'mem : U' ∈ F U := by
              simp only [hF, Finset.mem_filter]
              exact ⟨mem_vtxSet.mpr hvert', hdt⟩
            have := hsub hU'mem
            simp only [hF, Finset.mem_filter] at this
            exact lt_irrefl _ this.2
        have hlt : (F U').card < n := hcard ▸ Finset.card_lt_card hsub
        obtain ⟨Y, L, hW, hY⟩ := ih (F U').card hlt U' rfl hvert'
        exact ⟨Y, (i, U, U') :: L, WalkR.cons hS hW, hY⟩
      · push_neg at hstep
        exact ⟨U, [], WalkR.nil U, hstep⟩
  exact key _ X rfl hX

/-- **A maximal segment from `X` along `d`**: if a left tile and a right tile both start at `X` along `d`, the two maximal walks are nonempty and end at
the same point `Y`. -/
theorem exists_maxseg (D : Dissection N) {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X)
    (hl : ∃ i U', TriStep (D.tile i) d X U') (hr : ∃ i U', TriStep (D.tile i) (neg2 d) U' X) :
    ∃ Y L1 L2, WalkT D d X Y L1 ∧ WalkR D d X Y L2 ∧ L1 ≠ [] ∧ L2 ≠ [] ∧
      (∀ i U', ¬ TriStep (D.tile i) d Y U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y) := by
  obtain ⟨Y1, L1, W1, hno1⟩ := exists_maxwalkT D hd hX
  obtain ⟨Y2, L2, W2, hno2⟩ := exists_maxwalkR D hd hX
  have hL1 : L1 ≠ [] := by
    rintro rfl
    cases W1
    obtain ⟨i, U', hS⟩ := hl
    exact hno1 i U' hS
  have hL2 : L2 ≠ [] := by
    rintro rfl
    cases W2
    obtain ⟨i, U', hS⟩ := hr
    exact hno2 i U' hS
  have hY : Y1 = Y2 := ends_coincide D hd hL1 hL2 W1 W2 hno1 hno2
  subst hY
  exact ⟨Y1, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩

theorem walkR_dist_sum {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) : (L.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := walkR_progress W
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    have hXY : toV2 (Y - X) = ((c + T) * d.1, (c + T) * d.2) := by
      have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, h1]; ext <;> simp <;> ring
    have d1 := dist_of_toV2 hc.le h1
    have d2 := dist_of_toV2 hT hTe
    have d3 := dist_of_toV2 (by positivity : 0 ≤ c + T) hXY
    simp only [List.map_cons, List.sum_cons]
    rw [ih, dist_comm X X', d1, dist_comm X' Y, d2, dist_comm X Y, d3]
    ring

/-- A list of reals each equal to `a`, `b` or `c`: its sum is `n_a a + n_b b + n_c c`, with `n_b + n_c >= 1` as soon as some entry differs from `a`. -/
theorem sum_abc (a b c : ℝ) (ds : List ℝ) (h : ∀ x ∈ ds, x = a ∨ x = b ∨ x = c) :
    ∃ na nb nc : ℕ, ds.sum = na * a + nb * b + nc * c ∧ ((∃ x ∈ ds, x ≠ a) → 1 ≤ nb + nc) := by
  induction ds with
  | nil => exact ⟨0, 0, 0, by simp, by simp⟩
  | cons x ds ih =>
    obtain ⟨na, nb, nc, hs, hn⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self ..) with hx | hx | hx
    · refine ⟨na + 1, nb, nc, ?_, ?_⟩
      · simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring
      · rintro ⟨y, hy, hya⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hx hya
        · exact hn ⟨y, hy', hya⟩
    · refine ⟨na, nb + 1, nc, ?_, ?_⟩
      · simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring
      · intro _; omega
    · refine ⟨na, nb, nc + 1, ?_, ?_⟩
      · simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring
      · intro _; omega

/-- **The `A`-run of a division ends** (existence of the index `i_0` of Laczkovich's definition of `Γ_a`): if the first left side has length `a`, the first right side
does not, and the two divisions have the same total length, some left side is not `a`. -/
theorem arun_end (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} {X Y : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toDissection d X Y L1) (W2 : WalkR D.toDissection d X Y L2)
    {e1 e2 : Fin N × Plane × Plane} {L1' L2' : List (Fin N × Plane × Plane)} (h1 : L1 = e1 :: L1') (h2 : L2 = e2 :: L2')
    (hf2 : dist e2.2.1 e2.2.2 ≠ slen D 0) : ∃ e ∈ L1, dist e.2.1 e.2.2 ≠ slen D 0 := by
  by_contra hall
  push_neg at hall
  have hs1 := walkT_dist_sum W1
  have hs2 := walkR_dist_sum W2
  have hsum1 : (L1.map fun e => dist e.2.1 e.2.2).sum = L1.length • slen D 0 := by
    have : (L1.map fun e => dist e.2.1 e.2.2).sum = (L1.map fun e => dist e.2.1 e.2.2).length • slen D 0 := by
      apply List.sum_eq_card_nsmul
      intro x hx
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hall e' he'
    rw [this, List.length_map]
  have hmemR : ∀ e ∈ L2, dist e.2.1 e.2.2 = slen D 0 ∨ dist e.2.1 e.2.2 = slen D 1 ∨ dist e.2.1 e.2.2 = slen D 2 := by
    intro e he
    have := side_len_mem D idx hidx (walkR_mem_step W2 e he)
    rw [dist_comm] at this
    exact this
  obtain ⟨na, nb, nc, hsum2, hn⟩ := sum_abc (slen D 0) (slen D 1) (slen D 2) (L2.map fun e => dist e.2.1 e.2.2)
    (by
      intro x hx
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hmemR e' he')
  have hnb : 1 ≤ nb + nc := by
    apply hn
    refine ⟨dist e2.2.1 e2.2.2, ?_, hf2⟩
    apply List.mem_map.mpr
    exact ⟨e2, by rw [h2]; exact List.mem_cons_self .., rfl⟩
  have hEq : (L1.length : ℝ) * slen D 0 = na * slen D 0 + nb * slen D 1 + nc * slen D 2 := by
    have := hs1.trans hs2.symm
    rw [hsum1, hsum2] at this
    simpa [nsmul_eq_mul] using this
  have hb := slen_pos D 1
  have hc := slen_pos D 2
  have ha := slen_pos D 0
  have hpos : (0 : ℝ) < nb * slen D 1 + nc * slen D 2 := by
    by_cases hnb0 : nb = 0
    · have h1 : 1 ≤ nc := by omega
      have h2 : (1 : ℝ) ≤ nc := by exact_mod_cast h1
      subst hnb0
      simp only [Nat.cast_zero, zero_mul, zero_add]
      nlinarith
    · have h2 : (1 : ℝ) ≤ nb := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnb0
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) nc) hc.le]
  have hlt : (na : ℝ) < L1.length := by
    by_contra hge
    push_neg at hge
    nlinarith [mul_le_mul_of_nonneg_right hge ha.le]
  have hlt' : na < L1.length := by exact_mod_cast hlt
  refine hnc (L1.length - na) nb nc (by omega) ?_
  rw [Nat.cast_sub hlt'.le]
  linear_combination hEq

/-! ## The graph `Γ_a` -/

/-- `X` is the START of a maximal segment along `d`: no left or right tile side along the line covers `X` from behind (except at its own start). -/
def NoBack (D : Dissection N) (d : V2) (X : Plane) : Prop :=
  (∀ i A B (σ : ℝ), TriStep (D.tile i) d A B → 0 < σ → σ ≤ 1 → X ≠ A + σ • (B - A)) ∧
  (∀ i A B (σ : ℝ), TriStep (D.tile i) (neg2 d) A B → 0 < σ → σ ≤ 1 → X ≠ B + σ • (A - B))

/-- The division `L` (list of `(tile, tail, head)`) has its first non-`a` side at `e` with tail `H`, after a nonempty run of `a`-sides. -/
def RunEnd (a : ℝ) (L : List (Fin N × Plane × Plane)) (H : Plane) : Prop :=
  ∃ L' e L'', L = L' ++ e :: L'' ∧ L' ≠ [] ∧ (∀ x ∈ L', dist x.2.1 x.2.2 = a) ∧ dist e.2.1 e.2.2 ≠ a ∧ H = e.2.1

/-- **The edges of `Γ_a`** (Laczkovich, DCG 48 (2012), Sect. 4).  `X → H` iff `X` is the start of a maximal segment `XY` (two maximal nonempty divisions, left `L1` and right `L2`,
ending together at `Y`, lying in the closure of... see `ExtFan`), exactly one of the first sides has length `a`, and `H = U_{i_0}` is the end of the `a`-run of the division
whose first side is `a`. -/
def GaEdge (D : Dissection N) (a : ℝ) (X H : Plane) : Prop :=
  ∃ (d : V2) (Y : Plane) (L1 L2 : List (Fin N × Plane × Plane)),
    d ≠ 0 ∧ NoBack D d X ∧ WalkT D d X Y L1 ∧ WalkR D d X Y L2 ∧ L1 ≠ [] ∧ L2 ≠ [] ∧
    (∀ i U', ¬ TriStep (D.tile i) d Y U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y) ∧
    ((RunEnd a L1 H ∧ ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ a) ∨
     (RunEnd a L2 H ∧ ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ a))

/-- First non-`P` element of a list whose head satisfies `P`. -/
theorem list_first_not {α : Type*} (P : α → Prop) (L : List α) (hL : ∀ e ∈ L.head?, P e) (hne : L ≠ [])
    (hex : ∃ e ∈ L, ¬ P e) : ∃ L' e L'', L = L' ++ e :: L'' ∧ L' ≠ [] ∧ (∀ x ∈ L', P x) ∧ ¬ P e := by
  induction L with
  | nil => exact absurd rfl hne
  | cons x L ih =>
    have hx : P x := hL x (by simp)
    by_cases hL' : ∃ e ∈ L, ¬ P e
    · by_cases hLne : L = []
      · subst hLne; simp at hL'
      · -- either the head of L fails P, or recurse
        by_cases hh : ∀ e ∈ L.head?, P e
        · obtain ⟨L', e, L'', hL, hL'ne, hall, hnot⟩ := ih hh hLne hL'
          refine ⟨x :: L', e, L'', ?_, by simp, ?_, hnot⟩
          · rw [hL]; rfl
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hx
            · exact hall y hy'
        · push_neg at hh
          obtain ⟨e, he, hnot⟩ := hh
          cases L with
          | nil => simp at hLne
          | cons y L2 =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
            subst he
            exact ⟨[x], _, L2, rfl, by simp, by simpa using hx, hnot⟩
    · push_neg at hL'
      obtain ⟨e, he, hnot⟩ := hex
      rcases List.mem_cons.mp he with he1 | he'
      · rw [he1] at hnot; exact absurd hx hnot
      · exact absurd (hL' e he') hnot

theorem par_arm_neg {A B : Plane} {d : V2} (h : Par (toV2 (B - A)) (neg2 d)) : Par (toV2 (A - B)) d := by
  have := par_neg h
  rw [neg2_neg2] at this
  have e : toV2 (A - B) = (-(toV2 (B - A)).1, -(toV2 (B - A)).2) := by unfold toV2; ext <;> simp
  rw [e]; exact this

/-- The left tile starting at `X` along `d` is unique, and so is its far vertex. -/
theorem left_step_unique (D : Dissection N) {d : V2} {X : Plane} {i i' : Fin N} {U U' : Plane}
    (h1 : TriStep (D.tile i) d X U) (h2 : TriStep (D.tile i') d X U') : i = i' ∧ U = U' := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := id h2
  have hvert : ∃ j k, (D.tile j).pts k = X := ⟨i, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D X hvert
  have hmem : X ∈ (D.tile i).carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmem' : X ∈ (D.tile i').carrier := hk' ▸ subset_convexHull ℝ _ ⟨kk', rfl⟩
  set s : AtV D X := ⟨i, hmem⟩
  set s' : AtV D X := ⟨i', hmem'⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec s) ⟨kk, hk⟩
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec s') ⟨kk', hk'⟩
  have hps : Par (F.p s) d := triStep_start h1 kk2 fl2 hk2 hp2 hq2 (F.hok s)
  have hps' : Par (F.p s') d := triStep_start h2 kk3 fl3 hk3 hp3 hq3 (F.hok s')
  have hdis := tiles_disjoint D X F.p F.q F.hloc
  have hss : s = s' := by
    by_contra hne
    exact start_inj F.p F.q F.hok hdis hne (hps'.trans hps.symm)
  have hii : i = i' := congrArg Subtype.val hss
  subst hii
  refine ⟨rfl, ?_⟩
  have hkk : kk = kk' := (D.tile i).indep.injective (hk.trans hk'.symm)
  subst hkk
  have hff : f = f' := by
    apply arm_unique (D.tile i) X kk hk f f' hfk hfk' d
    · rw [← hf] at hpar; exact hpar
    · rw [← hf'] at hpar'; exact hpar'
  rw [← hf, ← hf', hff]

/-- The right tile ending at `X` along `d` is unique, and so is its far vertex. -/
theorem right_step_unique (D : Dissection N) {d : V2} {X : Plane} {i i' : Fin N} {U U' : Plane}
    (h1 : TriStep (D.tile i) (neg2 d) U X) (h2 : TriStep (D.tile i') (neg2 d) U' X) : i = i' ∧ U = U' := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := id h2
  have hvert : ∃ j k, (D.tile j).pts k = X := ⟨i, f, hf⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D X hvert
  have hmem : X ∈ (D.tile i).carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmem' : X ∈ (D.tile i').carrier := hf' ▸ subset_convexHull ℝ _ ⟨f', rfl⟩
  set s : AtV D X := ⟨i, hmem⟩
  set s' : AtV D X := ⟨i', hmem'⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec s) ⟨f, hf⟩
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec s') ⟨f', hf'⟩
  have hqs : Par (F.q s) (-(neg2 d).1, -(neg2 d).2) := triStep_end h1 kk2 fl2 hk2 hp2 hq2 (F.hok s)
  have hqs' : Par (F.q s') (-(neg2 d).1, -(neg2 d).2) := triStep_end h2 kk3 fl3 hk3 hp3 hq3 (F.hok s')
  have hdis := tiles_disjoint D X F.p F.q F.hloc
  have hss : s = s' := by
    by_contra hne
    exact end_inj' F.p F.q F.hok hdis hne (hqs'.trans hqs.symm)
  have hii : i = i' := congrArg Subtype.val hss
  subst hii
  refine ⟨rfl, ?_⟩
  have hff : f = f' := (D.tile i).indep.injective (hf.trans hf'.symm)
  subst hff
  have hP1 : Par (toV2 (U - X)) d := par_arm_neg hpar
  have hP2 : Par (toV2 (U' - X)) d := par_arm_neg hpar'
  have hkk : kk = kk' := by
    apply arm_unique (D.tile i) X f hf kk kk' hfk.symm hfk'.symm d
    · rw [hk]; exact hP1
    · rw [hk']; exact hP2
  rw [← hk, ← hk', hkk]

/-- **An edge of `Γ_a` starts at `X` from local data**: `X` is the start of a maximal segment along `d`, a left tile starts at `X` along `d` with first side `a`, and the
right tile starting at `X` has first side different from `a` (and `a` is not a nonnegative rational combination of `b, c`).  Then `Γ_a` has an edge out of `X`. -/
theorem ga_edge_of_local (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X : Plane}
    (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 = slen D 0)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X ≠ slen D 0) :
    ∃ H, GaEdge D.toDissection (slen D 0) X H := by
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toDissection hd hX ⟨i1, U1, hl⟩ ⟨i2, U2, hr⟩
  -- first elements
  obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) d e1.2.1 e1.2.2 ∧ e1.2.1 = X := by
    cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 d) e2.2.2 e2.2.1 ∧ e2.2.1 = X := by
    cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  rw [he1X] at hS1
  rw [he2X] at hS2
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toDissection hS1 hl
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toDissection hS2 hr
  have hd1 : dist e1.2.1 e1.2.2 = slen D 0 := by rw [he1X, hU1]; exact hla
  have hd2 : dist e2.2.1 e2.2.2 ≠ slen D 0 := by
    rw [he2X, hU2, dist_comm]; exact hra
  obtain ⟨e, he, hne⟩ := arun_end D idx hidx hnc W1 W2 hL1e hL2e hd2
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot⟩ := list_first_not (fun x : Fin N × Plane × Plane => dist x.2.1 x.2.2 = slen D 0) L1
    (by rw [hL1e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hd1)
    hL1 ⟨e, he, hne⟩
  refine ⟨e0.2.1, d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, Or.inl ⟨⟨L', e0, L'', hdec, hL'ne, hall, hnot, rfl⟩, ?_⟩⟩
  intro x hx
  rw [hL2e] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx]; exact hd2

end Erdos634.Draft.LaczFormal.Graph
