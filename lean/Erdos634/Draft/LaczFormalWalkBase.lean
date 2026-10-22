import Erdos634.Draft.LaczFormalGraphWalk
import Erdos634.Draft.LaczFormalGraphLocal

/-!
# Walks along a side of the target: parameters, adjacency, one step per tile

Erdős #634, base-`β` band.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: the walk along a side), AI assistant
(item 3), Beeson–Roșu, Beeson, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`WalkT D d X Y L` (LaczFormalGraphWalk) is the list of tile steps along a side.  Here, for a side
`X0 → Y0` with `d = toV2 (Y0 − X0)`:
* `walk_param`: the vertices of the walk are `X0 + s•(Y0 − X0)` with strictly increasing parameters;
* `walk_adjacent`, `walk_last`: consecutive entries share the junction, the last ends at `Y`;
* `tristep_unique`: a tile has at most one step on a given line (so consecutive entries use different tiles).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem eq_smul_of_toV2 {u w : Plane} {c : ℝ} (h : toV2 u = (c * (toV2 w).1, c * (toV2 w).2)) :
    u = c • w := by
  have h0 : u 0 = c * w 0 := congrArg Prod.fst h
  have h1 : u 1 = c * w 1 := congrArg Prod.snd h
  ext i; fin_cases i <;> simp [h0, h1]

theorem smul_injective_of_ne {w : Plane} (hw : w ≠ 0) {s t : ℝ} (h : s • w = t • w) : s = t := by
  by_contra hne
  apply hw
  have : (s - t) • w = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h') hne
  · exact h'

theorem tristep_vec {T : Tri} {d : V2} {U U' : Plane} (h : TriStep T d U U') {w : Plane}
    (hd : d = toV2 w) : ∃ c : ℝ, 0 < c ∧ U' = U + c • w := by
  obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := h
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  refine ⟨c, hc, ?_⟩
  have : U' - U = c • w := eq_smul_of_toV2 (by rw [hcw, hd])
  rw [← this]; abel

/-- **Parameters along a walk.** -/
theorem walk_param {D : Dissection N} {X0 Y0 : Plane} (hne : X0 ≠ Y0) {X Y : Plane}
    {L : List (Fin N × Plane × Plane)} (W : WalkT D (toV2 (Y0 - X0)) X Y L) {t0 t1 : ℝ}
    (hX : X = X0 + t0 • (Y0 - X0)) (hY : Y = X0 + t1 • (Y0 - X0)) :
    t0 ≤ t1 ∧ (∀ e ∈ L, ∃ s t : ℝ, t0 ≤ s ∧ s < t ∧ t ≤ t1 ∧
      e.2.1 = X0 + s • (Y0 - X0) ∧ e.2.2 = X0 + t • (Y0 - X0)) ∧ L.Nodup := by
  have hw : Y0 - X0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  induction W generalizing t0 with
  | nil X =>
    have : t0 • (Y0 - X0) = t1 • (Y0 - X0) := by
      have := hX.symm.trans hY
      exact add_left_cancel this
    have := smul_injective_of_ne hw this
    exact ⟨le_of_eq this, fun e he => absurd he (by simp), List.nodup_nil⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨c, hc, hX'⟩ := tristep_vec hS rfl
    have hX'p : X' = X0 + (t0 + c) • (Y0 - X0) := by rw [hX', hX, add_smul]; abel
    obtain ⟨h01, hall, hnd⟩ := ih hX'p hY
    refine ⟨by linarith, fun e he => ?_, ?_⟩
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨t0, t0 + c, le_rfl, by linarith, by linarith, hX, hX'p⟩
      · obtain ⟨s, t, h1, h2, h3, h4, h5⟩ := hall e he'
        exact ⟨s, t, by linarith, h2, h3, h4, h5⟩
    · refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩
      obtain ⟨s, t, h1, h2, h3, h4, h5⟩ := hall _ hmem
      have : X0 + s • (Y0 - X0) = X0 + t0 • (Y0 - X0) := h4.symm.trans hX
      have := smul_injective_of_ne hw (add_left_cancel this)
      linarith

theorem walk_adjacent {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ (s t : List (Fin N × Plane × Plane)) (a b : Fin N × Plane × Plane),
    L = s ++ a :: b :: t → a.2.2 = b.2.1 := by
  induction W with
  | nil X => intro s t a b h; simp at h
  | @cons i X X' Y L hS W ih =>
    intro s t a b h
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      cases W with
      | nil => simp at h2
      | cons hS' W' =>
        simp only [List.cons.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        rfl
    | cons c s' =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih s' t a b h.2

theorem walk_last {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ (s : List (Fin N × Plane × Plane)) (a : Fin N × Plane × Plane),
    L = s ++ [a] → a.2.2 = Y := by
  induction W with
  | nil X => intro s a h; simp at h
  | @cons i X X' Y L hS W ih =>
    intro s a h
    cases s with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      cases W with
      | nil => rfl
      | cons _ _ => simp at h2
    | cons c s' =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih s' a h.2

theorem walk_first {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ (a : Fin N × Plane × Plane) (t : List (Fin N × Plane × Plane)),
    L = a :: t → a.2.1 = X := by
  intro a t h
  cases W with
  | nil => simp at h
  | cons hS W' =>
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl

theorem fin3_other (kk f g x : Fin 3) (h1 : kk ≠ f) (h2 : kk ≠ g) (h3 : f ≠ g) (hx : x ≠ g) :
    x = kk ∨ x = f := by
  revert kk f g x; decide

/-- **A tile has at most one step on a line**: two steps `U → U'`, `V → V'` of the same tile along `d`, `V`
on the line through `U` with direction `d`, coincide. -/
theorem tristep_unique {T : Tri} {d : V2} {U U' V V' : Plane} (h1 : TriStep T d U U')
    (h2 : TriStep T d V V') (hcol : crs d (toV2 (V - U)) = 0) : U = V ∧ U' = V' := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := h2
  have hd1 : crs d (toV2 (U' - U)) = 0 := by
    have := hpar.1; unfold crs at this ⊢; linarith
  have hd2 : crs d (toV2 (V' - V)) = 0 := by
    have := hpar'.1; unfold crs at this ⊢; linarith
  -- vertices on the line are not `g`
  have hline : ∀ P : Plane, crs d (toV2 (P - U)) = 0 → T.pts g ≠ P := by
    intro P hP hgP
    rw [← hgP] at hP
    exact absurd hP hleft.ne'
  have hVline : crs d (toV2 (V - U)) = 0 := hcol
  have hV'line : crs d (toV2 (V' - U)) = 0 := by
    have : toV2 (V' - U) = ((toV2 (V' - V)).1 + (toV2 (V - U)).1, (toV2 (V' - V)).2 + (toV2 (V - U)).2) := by
      unfold toV2; ext <;> simp
    rw [this]; unfold crs at hd2 hVline ⊢; simp only at hd2 hVline ⊢; linarith
  have hk'g : kk' ≠ g := by
    intro h; apply hline V hVline; rw [← hk', h]
  have hf'g : f' ≠ g := by
    intro h; apply hline V' hV'line; rw [← hf', h]
  have hkk' := fin3_other kk f g kk' hfk.symm hgk.symm hgf.symm hk'g
  have hff' := fin3_other kk f g f' hfk.symm hgk.symm hgf.symm hf'g
  rcases hkk' with rfl | rfl
  · rcases hff' with rfl | rfl
    · exact absurd rfl hfk'
    · rw [← hk, ← hk', ← hf, ← hf']; exact ⟨rfl, rfl⟩
  · rcases hff' with rfl | rfl
    · -- (kk', f') = (f, kk): opposite orientation
      exfalso
      have e1 : V = U' := by rw [← hk', ← hf]
      have e2 : V' = U := by rw [← hf', ← hk]
      have p1 := hpar.2
      have p2 := hpar'.2
      rw [e1, e2] at p2
      unfold dt toV2 at p1 p2
      simp only [Prod.mk.injEq, PiLp.sub_apply] at p1 p2
      nlinarith
    · exact absurd rfl hfk'


/-- **The walk covers the side**: every parameter `m ∈ [t0, t1]` lies in the parameter interval of some entry. -/
theorem walk_cover {D : Dissection N} {X0 Y0 : Plane} (hne : X0 ≠ Y0) {X Y : Plane}
    {L : List (Fin N × Plane × Plane)} (W : WalkT D (toV2 (Y0 - X0)) X Y L) {t0 t1 : ℝ}
    (hX : X = X0 + t0 • (Y0 - X0)) (hY : Y = X0 + t1 • (Y0 - X0)) (hlt : t0 < t1) :
    ∀ m : ℝ, t0 ≤ m → m ≤ t1 → ∃ e ∈ L, ∃ s t : ℝ, s ≤ m ∧ m ≤ t ∧ s < t ∧
      e.2.1 = X0 + s • (Y0 - X0) ∧ e.2.2 = X0 + t • (Y0 - X0) := by
  have hw : Y0 - X0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  induction W generalizing t0 with
  | nil X =>
    have : t0 • (Y0 - X0) = t1 • (Y0 - X0) := add_left_cancel (hX.symm.trans hY)
    have := smul_injective_of_ne hw this
    linarith
  | @cons i X X' Y L hS W ih =>
    intro m hm0 hm1
    obtain ⟨c, hc, hX'⟩ := tristep_vec hS rfl
    have hX'p : X' = X0 + (t0 + c) • (Y0 - X0) := by rw [hX', hX, add_smul]; abel
    by_cases hmc : m ≤ t0 + c
    · exact ⟨(i, X, X'), List.mem_cons_self, t0, t0 + c, hm0, hmc, by linarith, hX, hX'p⟩
    · have hle := (walk_param hne W hX'p hY).1
      have hlt' : t0 + c < t1 := by
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso; apply hmc; linarith
      obtain ⟨e, he, s, t, h1, h2, h3, h4, h5⟩ := ih hX'p hY hlt' m (by linarith) hm1
      exact ⟨e, List.mem_cons_of_mem _ he, s, t, h1, h2, h3, h4, h5⟩

end Erdos634.LaczJunction.Walk
