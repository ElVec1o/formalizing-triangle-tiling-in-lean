-- Draft/LaczFormalGraphIn.lean -- D2 (part 3): IN-DEGREE <= 1 of Gamma_a (Laczkovich, DCG 48 (2012), Lemma 8.1 / Sect. 4 "in-degree").
-- (1) covering of a walk by half-open parameter intervals `(t0, t1]`; (2) `NoBack` forbids a point strictly inside the walk of another edge;
-- (3) the straight sector at a head is unique, a corner sector is determined by its starting ray;
-- (4) `ga_indegree`: `GaEdge X H` and `GaEdge X' H` give `X = X'`.  UNAUDITED.  Credit: Laczkovich, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalGraphFour
import Erdos634.Draft.LaczFormalCondE

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem walkT_cover' {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 < s → s ≤ T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 < s ∧ s ≤ t1 := by
  induction W generalizing T with
  | nil X =>
    intro s hs hsT
    exfalso
    have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hT; simpa [toV2] using this.symm
    have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hT; simpa [toV2] using this.symm
    have hT0 : T = 0 := by
      by_contra hne
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))
    linarith
  | @cons i X X' Y L hS W ih =>
    intro s hs hsT
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    by_cases hsc : s ≤ c
    · exact ⟨(i, X, X'), List.mem_cons_self .., 0, c, by unfold toV2; ext <;> simp, hcw, hs, hsc⟩
    · push_neg at hsc
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        have : toV2 (Y - X') = ((toV2 (Y - X)).1 - (toV2 (X' - X)).1, (toV2 (Y - X)).2 - (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hT, hcw]; ext <;> simp <;> ring
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := ih hT' (s - c) (by linarith) (by linarith)
      refine ⟨e, List.mem_cons_of_mem _ he, t0 + c, t1 + c, ?_, ?_, by linarith, by linarith⟩
      · have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h0, hcw]; ext <;> simp <;> ring
      · have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h1, hcw]; ext <;> simp <;> ring

theorem walkR_cover' {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 < s → s ≤ T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 < s ∧ s ≤ t1 := by
  induction W generalizing T with
  | nil X =>
    intro s hs hsT
    exfalso
    have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hT; simpa [toV2] using this.symm
    have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hT; simpa [toV2] using this.symm
    have hT0 : T = 0 := by
      by_contra hne
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))
    linarith
  | @cons i X X' Y L hS W ih =>
    intro s hs hsT
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    by_cases hsc : s ≤ c
    · exact ⟨(i, X, X'), List.mem_cons_self .., 0, c, by unfold toV2; ext <;> simp, h1, hs, hsc⟩
    · push_neg at hsc
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        have : toV2 (Y - X') = ((toV2 (Y - X)).1 - (toV2 (X' - X)).1, (toV2 (Y - X)).2 - (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hT, h1]; ext <;> simp <;> ring
      obtain ⟨e, he, t0, t1, h0, h1', h2, h3⟩ := ih hT' (s - c) (by linarith) (by linarith)
      refine ⟨e, List.mem_cons_of_mem _ he, t0 + c, t1 + c, ?_, ?_, by linarith, by linarith⟩
      · have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h0, h1]; ext <;> simp <;> ring
      · have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h1', h1]; ext <;> simp <;> ring

/-- The point `P` with `toV2 (P - A) = t * d` etc. is the convex combination: helper for the `NoBack` contradictions. -/
theorem pt_on_step {X A B P : Plane} {d : V2} {t0 t1 s : ℝ} (h0 : t0 < s) (h1 : s ≤ t1)
    (hA : toV2 (A - X) = (t0 * d.1, t0 * d.2)) (hB : toV2 (B - X) = (t1 * d.1, t1 * d.2))
    (hP : toV2 (P - X) = (s * d.1, s * d.2)) :
    P = A + ((s - t0) / (t1 - t0)) • (B - A) := by
  have hne : t1 - t0 ≠ 0 := by intro h; linarith
  apply pt_eq_of_toV2 (H := X)
  have a1 := congrArg Prod.fst hA
  have a2 := congrArg Prod.snd hA
  have b1 := congrArg Prod.fst hB
  have b2 := congrArg Prod.snd hB
  simp only [toV2, PiLp.sub_apply] at a1 a2 b1 b2 hP ⊢
  rw [hP]
  ext <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> field_simp <;> nlinarith [a1, a2, b1, b2]

theorem noBack_walkT {D : Dissection N} {d : V2} (hd : d ≠ 0) {X H X' : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X H L) {T s : ℝ} (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hs0 : 0 < s) (hsT : s ≤ T)
    (hX' : toV2 (X' - X) = (s * d.1, s * d.2)) (hnb : NoBack D d X') : False := by
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover' W hT hd s hs0 hsT
  have hS := walkT_mem_step W e he
  have hne : t0 < t1 := lt_of_lt_of_le h2 h3
  have hσ0 : 0 < (s - t0) / (t1 - t0) := div_pos (by linarith) (by linarith)
  have hσ1 : (s - t0) / (t1 - t0) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  exact hnb.1 e.1 e.2.1 e.2.2 _ hS hσ0 hσ1 (pt_on_step h2 h3 h0 h1 hX')

theorem noBack_walkR {D : Dissection N} {d : V2} (hd : d ≠ 0) {X H X' : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X H L) {T s : ℝ} (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hs0 : 0 < s) (hsT : s ≤ T)
    (hX' : toV2 (X' - X) = (s * d.1, s * d.2)) (hnb : NoBack D d X') : False := by
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover' W hT hd s hs0 hsT
  have hS := walkR_mem_step W e he
  have hne : t0 < t1 := lt_of_lt_of_le h2 h3
  have hσ0 : 0 < (s - t0) / (t1 - t0) := div_pos (by linarith) (by linarith)
  have hσ1 : (s - t0) / (t1 - t0) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  exact hnb.2 e.1 e.2.2 e.2.1 _ hS hσ0 hσ1 (pt_on_step h2 h3 h0 h1 hX')

/-- Position algebra for two edges ending at the same point `H` along parallel directions. -/
theorem xuniq_core {d d' : V2} (hpar : Par d' d) {X X' H : Plane} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (h1 : toV2 (H - X) = (T * d.1, T * d.2)) (h2 : toV2 (H - X') = (T' * d'.1, T' * d'.2)) :
    X = X' ∨ (0 < T - T' * (Classical.choose hpar.smul) ∧ toV2 (X' - X) = ((T - T' * (Classical.choose hpar.smul)) * d.1, (T - T' * (Classical.choose hpar.smul)) * d.2)) ∨
      (0 < T' - T / (Classical.choose hpar.smul) ∧ toV2 (X - X') = ((T' - T / (Classical.choose hpar.smul)) * d'.1, (T' - T / (Classical.choose hpar.smul)) * d'.2)) := by
  obtain ⟨hc, hcd⟩ := Classical.choose_spec hpar.smul
  set c := Classical.choose hpar.smul
  have hd1 : d'.1 = c * d.1 := by rw [hcd]
  have hd2 : d'.2 = c * d.2 := by rw [hcd]
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have f1 := congrArg Prod.fst h2
  have f2 := congrArg Prod.snd h2
  simp only [toV2, PiLp.sub_apply] at e1 e2 f1 f2
  rcases lt_trichotomy (T - T' * c) 0 with hlt | heq | hgt
  · right; right
    have hpos : 0 < T' - T / c := by
      have : T / c < T' := by rw [div_lt_iff₀ hc]; linarith
      linarith
    refine ⟨hpos, ?_⟩
    simp only [toV2, PiLp.sub_apply]
    have hcne : c ≠ 0 := hc.ne'
    ext
    · show X 0 - X' 0 = (T' - T / c) * d'.1
      rw [hd1]; field_simp; nlinarith [e1, f1, hd1]
    · show X 1 - X' 1 = (T' - T / c) * d'.2
      rw [hd2]; field_simp; nlinarith [e2, f2, hd2]
  · left
    have : T = T' * c := by linarith
    apply pt_eq_of_toV2 (H := H)
    simp only [toV2, PiLp.sub_apply]
    rw [hd1] at f1; rw [hd2] at f2
    rw [this] at e1 e2
    ext
    · show X 0 - H 0 = X' 0 - H 0
      nlinarith [e1, f1]
    · show X 1 - H 1 = X' 1 - H 1
      nlinarith [e2, f2]
  · right; left
    refine ⟨hgt, ?_⟩
    simp only [toV2, PiLp.sub_apply]
    ext
    · show X' 0 - X 0 = (T - T' * c) * d.1
      rw [hd1] at f1; nlinarith [e1, f1]
    · show X' 1 - X 1 = (T - T' * c) * d.2
      rw [hd2] at f2; nlinarith [e2, f2]

theorem xuniq_T {D : Dissection N} {d d' : V2} (hd : d ≠ 0) (hpar : Par d' d) {X X' H : Plane}
    {P P' : List (Fin N × Plane × Plane)} (W : WalkT D d X H P) (hP : P ≠ []) (W' : WalkT D d' X' H P') (hP' : P' ≠ [])
    (hnb : NoBack D d X) (hnb' : NoBack D d' X') : X = X' := by
  obtain ⟨T, -, hT, hTp⟩ := walkT_progress W
  obtain ⟨T', -, hT', hTp'⟩ := walkT_progress W'
  rcases xuniq_core hpar (hTp hP) (hTp' hP') hT hT' with h | ⟨hpos, hX'⟩ | ⟨hpos, hX⟩
  · exact h
  · exact (noBack_walkT hd W hT hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T' * Classical.choose hpar.smul := mul_pos (hTp' hP') this.1
      linarith) hX' (NoBack.of_par hpar.symm hnb')).elim
  · exact (noBack_walkT hpar.ne_left W' hT' hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T / Classical.choose hpar.smul := div_pos (hTp hP) this.1
      linarith) hX (NoBack.of_par hpar hnb)).elim

theorem xuniq_R {D : Dissection N} {d d' : V2} (hd : d ≠ 0) (hpar : Par d' d) {X X' H : Plane}
    {P P' : List (Fin N × Plane × Plane)} (W : WalkR D d X H P) (hP : P ≠ []) (W' : WalkR D d' X' H P') (hP' : P' ≠ [])
    (hnb : NoBack D d X) (hnb' : NoBack D d' X') : X = X' := by
  obtain ⟨T, -, hT, hTp⟩ := walkR_progress W
  obtain ⟨T', -, hT', hTp'⟩ := walkR_progress W'
  rcases xuniq_core hpar (hTp hP) (hTp' hP') hT hT' with h | ⟨hpos, hX'⟩ | ⟨hpos, hX⟩
  · exact h
  · exact (noBack_walkR hd W hT hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T' * Classical.choose hpar.smul := mul_pos (hTp' hP') this.1
      linarith) hX' (NoBack.of_par hpar.symm hnb')).elim
  · exact (noBack_walkR hpar.ne_left W' hT' hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T / Classical.choose hpar.smul := div_pos (hTp hP) this.1
      linarith) hX (NoBack.of_par hpar hnb)).elim

/-- **Two straight sectors and a corner do not fit around a point**: the straight sector at a head is unique. -/
theorem straight_unique {D : Dissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {s1 s2 a : AtV D V}
    (h1 : F.q s1 = (-(F.p s1).1, -(F.p s1).2)) (h2 : F.q s2 = (-(F.p s2).1, -(F.p s2).2))
    (ha : 0 < crs (F.p a) (F.q a)) : s1 = s2 := by
  classical
  by_contra hne
  have has1 : a ≠ s1 := by
    rintro rfl; rw [h1] at ha; unfold crs at ha; simp at ha; linarith
  have has2 : a ≠ s2 := by
    rintro rfl; rw [h2] at ha; unfold crs at ha; simp at ha; linarith
  have w1 : wd (F.p s1) (F.q s1) = Real.pi := by rw [h1]; exact wd_straight (F.hok s1).ne_p
  have w2 : wd (F.p s2) (F.q s2) = Real.pi := by rw [h2]; exact wd_straight (F.hok s2).ne_p
  have hsum := F.hsum
  have hvirt : 0 ≤ ∑ j, wd (F.pe j) (F.qe j) := Finset.sum_nonneg (fun j _ => (wd_pos (F.hokE j)).le)
  have h3 : wd (F.p s1) (F.q s1) + wd (F.p s2) (F.q s2) + wd (F.p a) (F.q a) ≤ ∑ x, wd (F.p x) (F.q x) := by
    have hsub : ({s1, s2, a} : Finset (AtV D V)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x => wd (F.p x) (F.q x)) hsub
      (fun x _ _ => (wd_pos (F.hok x)).le)
    rw [Finset.sum_insert (by simp [hne, Ne.symm has1]), Finset.sum_pair (Ne.symm has2)] at this
    linarith
  have := wd_pos (F.hok a)
  linarith

/-- A corner sector is determined by its starting ray (two corners with the same starting ray overlap). -/
theorem corner_start_unique {D : Dissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {x y : AtV D V}
    (hx : 0 < crs (F.p x) (F.q x)) (hy : 0 < crs (F.p y) (F.q y)) (hpar : Par (F.p x) (F.p y)) : x = y := by
  classical
  by_contra hne
  obtain ⟨δx, hδx, Hx⟩ := plus_ray_int (F.hok x)
  obtain ⟨δy, hδy, Hy⟩ := plus_ray_int (F.hok y)
  obtain ⟨c, hc, hcd⟩ := hpar.smul
  -- z = zplus (p y) ε lies in the cone of y; c * z lies... use ε small for both
  set ε := min δx δy / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεx : ε < δx := by have := min_le_left δx δy; linarith
  have hεy : ε < δy := by have := min_le_right δx δy; linarith
  have hzx := Hx ε hε0 hεx
  have hzy := Hy ε hε0 hεy
  have hzeq : zplus (F.p x) ε = (c * (zplus (F.p y) ε).1, c * (zplus (F.p y) ε).2) := by
    unfold zplus; rw [hcd]; ext <;> simp <;> ring
  rw [hzeq] at hzx
  have hzy' := (inInt_smul hc hzy)
  exact F.disj_all (o1 := Sum.inl x) (o2 := Sum.inl y) (fun h => hne (Sum.inl.inj h)) _ ⟨by simpa using hzx, by simpa using hzy'⟩

/-- The head of a `Γ_a` edge is a vertex of a tile. -/
theorem ga_edge_vertex (D : Dissection N) (a : ℝ) {X H : Plane} (h : GaEdge D a X H) : ∃ i k, (D.tile i).pts k = H := by
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -, -, hcase⟩ := h
  rcases hcase with ⟨⟨L', e, L'', hdec, -, -, -, hH⟩, -⟩ | ⟨⟨L', e, L'', hdec, -, -, -, hH⟩, -⟩
  · have hmem : e ∈ L1 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨kk, f, g, hk, -⟩ := walkT_mem_step W1 e hmem
    exact ⟨e.1, kk, hH ▸ hk⟩
  · have hmem : e ∈ L2 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨kk, f, g, hk, hf, -⟩ := walkR_mem_step W2 e hmem
    exact ⟨e.1, f, hH ▸ hf⟩

/-- Sector data at the head of a left-case edge. -/
def LeftF (D : CongruentDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toDissection H κ) (d : V2)
    (a b s : AtV D.toDissection H) : Prop :=
  0 < crs (F.p a) (F.q a) ∧ Par (F.q a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.p b) d ∧
    Par (F.p s) (neg2 d) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧ nsq (F.q a) = slen D 0 ^ 2 ∧ nsq (F.p b) ≠ slen D 0 ^ 2

/-- Sector data at the head of a right-case edge. -/
def RightF (D : CongruentDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toDissection H κ) (d : V2)
    (a b s : AtV D.toDissection H) : Prop :=
  0 < crs (F.p a) (F.q a) ∧ Par (F.p a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.q b) d ∧
    Par (F.p s) d ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧ nsq (F.p a) = slen D 0 ^ 2 ∧ nsq (F.q b) ≠ slen D 0 ^ 2

theorem ga_edge_data (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X H : Plane} (h : GaEdge D.toDissection (slen D 0) X H)
    {κ : Type} [Fintype κ] (F : ExtFan D.toDissection H κ) :
    ∃ d : V2, d ≠ 0 ∧ NoBack D.toDissection d X ∧
      ((∃ P, WalkT D.toDissection d X H P ∧ P ≠ [] ∧ ∃ a b s, LeftF D F d a b s) ∨
       (∃ P, WalkR D.toDissection d X H P ∧ P ≠ [] ∧ ∃ a b s, RightF D F d a b s)) := by
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -, -, hcase⟩ := h
  refine ⟨d, hd, hnb, ?_⟩
  rcases hcase with ⟨hRun, hR2⟩ | ⟨hRun, hL1'⟩
  · left
    have hRun0 := hRun
    obtain ⟨L', e, L'', hdec, hL'ne, -, -, hH⟩ := hRun
    obtain ⟨hpre, -⟩ := walkT_split W1 hdec
    refine ⟨L', hH ▸ hpre, hL'ne, ?_⟩
    obtain ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      ga_head_sectors_left D idx hidx hnc hd W1 W2 hRun0 hR2 F
    exact ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · right
    have hRun0 := hRun
    obtain ⟨L', e, L'', hdec, hL'ne, -, -, hH⟩ := hRun
    obtain ⟨hpre, -⟩ := walkR_split W2 hdec
    refine ⟨L', hH ▸ hpre, hL'ne, ?_⟩
    obtain ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      ga_head_sectors_right D idx hidx hnc hd W1 W2 hRun0 hL1' F
    exact ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem par_neg2 {u v : V2} (h : Par (neg2 u) (neg2 v)) : Par u v := by
  have := par_neg h
  rwa [neg2_neg2, neg2_neg2] at this

/-- A left-type and a right-type head configuration at the same vertex cannot coexist: the run ends would be the same corner with
side length `a` and `≠ a`. -/
theorem left_right_contra (D : CongruentDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toDissection H κ)
    {d d' : V2} {a b s a' b' s' : AtV D.toDissection H} (hl : LeftF D F d a b s) (hr : RightF D F d' a' b' s') : False := by
  obtain ⟨hca, hqa, hcb, hpb, hps, hqs, hna, hnb⟩ := hl
  obtain ⟨hca', hpa', hcb', hqb', hps', hqs', hna', hnb'⟩ := hr
  have hss : s = s' := straight_unique F hqs hqs' hca
  subst hss
  -- Par d' (neg2 d)
  have h1 : Par d' (neg2 d) := hps'.symm.trans hps
  have h2 : Par (neg2 d') d := by
    have := par_neg h1
    rwa [neg2_neg2] at this
  have h3 : Par (F.p a') (F.p b) := hpa'.trans (h2.trans hpb.symm)
  have hab : a' = b := corner_start_unique F hca' hcb h3
  subst hab
  exact hnb hna'

theorem ga_indegree (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X X' H : Plane}
    (h1 : GaEdge D.toDissection (slen D 0) X H) (h2 : GaEdge D.toDissection (slen D 0) X' H) : X = X' := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D.toDissection H (ga_edge_vertex _ _ h1)
  obtain ⟨d1, hd1, nb1, c1⟩ := ga_edge_data D idx hidx hnc h1 F
  obtain ⟨d2, hd2, nb2, c2⟩ := ga_edge_data D idx hidx hnc h2 F
  rcases c1 with ⟨P, W, hP, a, b, s, hf⟩ | ⟨P, W, hP, a, b, s, hf⟩ <;>
  rcases c2 with ⟨P', W', hP', a', b', s', hf'⟩ | ⟨P', W', hP', a', b', s', hf'⟩
  · -- left, left
    have hss : s = s' := straight_unique F hf.2.2.2.2.2.1 hf'.2.2.2.2.2.1 hf.1
    subst hss
    have hpar : Par d2 d1 := par_neg2 (hf'.2.2.2.2.1.symm.trans hf.2.2.2.2.1)
    exact xuniq_T hd1 hpar W hP W' hP' nb1 nb2
  · exact (left_right_contra D F hf hf').elim
  · exact (left_right_contra D F hf' hf).elim
  · -- right, right
    have hss : s = s' := straight_unique F hf.2.2.2.2.2.1 hf'.2.2.2.2.2.1 hf.1
    subst hss
    have hpar : Par d2 d1 := hf'.2.2.2.2.1.symm.trans hf.2.2.2.2.1
    exact xuniq_R hd1 hpar W hP W' hP' nb1 nb2

/-- **In-degree of `Γ_k`**: if at most three tiles have `β` at `X`, two `Γ_k` edges into `X` have the same tail (each edge uses two tiles with `β` at `X`,
and a tile has a single `γ`). -/
theorem gk_indegree (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {Z Z' X : Plane}
    (hc : cnt D idx X 1 ≤ 3) (h : GkEdge D.toDissection idx Z X) (h' : GkEdge D.toDissection idx Z' X) : Z = Z' := by
  classical
  by_contra hne
  obtain ⟨i, j, k1, k2, k1', k2', hij, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  obtain ⟨i', j', l1, l2, l1', l2', hij', c1, c2, c3, c4, c5, c6, c7, c8⟩ := h'
  have gam : ∀ (t : Fin N) (m m' : Fin 3), idx t m = 2 → idx t m' = 2 → m = m' := fun t m m' e e' =>
    (idx t).injective (e.trans e'.symm)
  have noeq : ∀ (t t' : Fin N) (m m' : Fin 3), t = t' → (D.tile t).pts m = Z → idx t m = 2 → (D.tile t').pts m' = Z' →
      idx t' m' = 2 → False := by
    intro t t' m m' htt hm em hm' em'
    subst htt
    exact hne (hm.symm.trans ((congrArg _ (gam t m m' em em')).trans hm'))
  let S : Finset (Fin N × Fin 3) := Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = X ∧ idx p.1 p.2 = 1)
  have m1 : (i, k2) ∈ S := by simp [S, a2, a6]
  have m2 : (j, k2') ∈ S := by simp [S, a4, a8]
  have m3 : (i', l2) ∈ S := by simp [S, c2, c6]
  have m4 : (j', l2') ∈ S := by simp [S, c4, c8]
  have n12 : (i, k2) ≠ (j, k2') := fun e => hij (congrArg Prod.fst e)
  have n34 : (i', l2) ≠ (j', l2') := fun e => hij' (congrArg Prod.fst e)
  have n13 : (i, k2) ≠ (i', l2) := fun e => noeq i i' k1 l1 (congrArg Prod.fst e) a1 a5 c1 c5
  have n14 : (i, k2) ≠ (j', l2') := fun e => noeq i j' k1 l1' (congrArg Prod.fst e) a1 a5 c3 c7
  have n23 : (j, k2') ≠ (i', l2) := fun e => noeq j i' k1' l1 (congrArg Prod.fst e) a3 a7 c1 c5
  have n24 : (j, k2') ≠ (j', l2') := fun e => noeq j j' k1' l1' (congrArg Prod.fst e) a3 a7 c3 c7
  have hsub : ({(i, k2), (j, k2'), (i', l2), (j', l2')} : Finset (Fin N × Fin 3)) ⊆ S := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({(i, k2), (j, k2'), (i', l2), (j', l2')} : Finset (Fin N × Fin 3)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair n34]
    · simp [n23, n24]
    · simp [n12, n13, n14]
  have := Finset.card_le_card hsub
  have hS : S.card = cnt D idx X 1 := rfl
  omega

end Erdos634.Draft.LaczFormal.Graph
