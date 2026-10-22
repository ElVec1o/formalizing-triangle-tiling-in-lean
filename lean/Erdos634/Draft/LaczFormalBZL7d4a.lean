-- Draft/LaczFormalBZL7d4a.lean -- Beeson-Zhang (arXiv 2604.01314v1) proof of Lemma 3.4, the step "there is at least one c edge on AC" (formal, polygon version):
-- if every tile edge on a side of the polygon had length a or b, each such tile would have its gamma corner on that edge; a vertex interior to the side has angle sum pi, so carries at most one gamma;
-- and no polygon vertex carries a gamma.  Induction along the walk of tiles on the side.
--   `step_gamma`        : a tile edge of length != c has a gamma corner at one of its endpoints;
--   `walk_pos`          : positions of the vertices of a walk along d;
--   `walk_mid_asum`     : a non-first vertex of the walk along side i has corner-angle sum pi (it is a non-corner boundary vertex);
--   `steps_tile_ne`     : two consecutive steps of a walk are from different tiles;
--   `walk_gamma_first`  : walk of non-c edges => the first tile has its gamma at the start;
--   `side_has_c`        : every side of the polygon has a tile edge of length c   (hypothesis: no gamma at any polygon vertex).
-- NOTE, UNAUDITED.  Credit: Beeson-Zhang (arXiv 2604.01314v1, proof of Lemma 3.4), Laczkovich (DCG 48 (2012), Sect. 4), Beeson.
import Erdos634.Draft.LaczFormalBZL7d1

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The tile `j` has a corner of model type `gamma` at `Z`. -/
def GamAt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (j : Fin N) (Z : Plane) : Prop :=
  ∃ k, (D.tile j).pts k = Z ∧ idx j k = 2

theorem gamAt_cnt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {j : Fin N} {Z : Plane} (h : GamAt D idx j Z) : 1 ≤ cnt D idx Z 2 := by
  obtain ⟨k, hk, hi⟩ := h
  unfold cnt
  apply Finset.card_pos.mpr
  exact ⟨(j, k), by simp [hk, hi]⟩

theorem two_tiles_two_gamma (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {j j' : Fin N} {Z : Plane} (hne : j ≠ j')
    (h1 : GamAt D idx j Z) (h2 : GamAt D idx j' Z) : 2 ≤ cnt D idx Z 2 := by
  obtain ⟨k1, a1, b1⟩ := h1
  obtain ⟨k2, a2, b2⟩ := h2
  unfold cnt
  have : ({(j, k1), (j', k2)} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = Z ∧ idx p.1 p.2 = 2) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card this
  rw [Finset.card_pair (fun e => hne (congrArg Prod.fst e))] at h3
  exact h3

/-- A tile edge whose length is not `c` has a gamma corner at one of its endpoints. -/
theorem step_gamma (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile j) d U U') (hne : dist U U' ≠ slen D 2) :
    GamAt D idx j U ∨ GamAt D idx j U' := by
  obtain ⟨kk, f, g, hk, hf, hfk, -, -, -, -⟩ := hS
  have hd := hidx j kk f
  rw [hk, hf] at hd
  have hpq : idx j kk ≠ idx j f := fun e => hfk ((idx j).injective e).symm
  by_cases h1 : idx j kk = 2
  · exact Or.inl ⟨kk, hk, h1⟩
  by_cases h2 : idx j f = 2
  · exact Or.inr ⟨f, hf, h2⟩
  have s2 : slen D 2 = dist (D.model.pts 0) (D.model.pts 1) := by
    have e1 : (2 : Fin 3) + 1 = 0 := by decide
    have e2 : (2 : Fin 3) + 2 = 1 := by decide
    unfold slen; rw [e1, e2]
  have key : dist (D.model.pts (idx j kk)) (D.model.pts (idx j f)) = dist (D.model.pts 0) (D.model.pts 1) := by
    revert hpq h1 h2
    generalize idx j kk = p
    generalize idx j f = q
    intro hpq h1 h2
    fin_cases p <;> fin_cases q <;> first | rfl | exact dist_comm _ _ | (exfalso; simp_all)
  exact absurd (by rw [hd, key, s2]) hne

/-- A vertex interior to a side (corner-angle sum `π`) carries at most one `γ` corner. -/
theorem cnt_gamma_le_one (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) {Z : Plane}
    (hA : Asum D idx Z = Real.pi) : cnt D idx Z 2 ≤ 1 := by
  have hpos : ∀ l, 0 < D.model.angleAt l := model_angle_pos' D
  have h : (cnt D idx Z 2 : ℝ) * D.model.angleAt 2 ≤ Real.pi := by
    rw [← hA]
    unfold Asum
    exact Finset.single_le_sum (f := fun l => (cnt D idx Z l : ℝ) * D.model.angleAt l) (fun l _ => mul_nonneg (Nat.cast_nonneg _) (hpos l).le) (Finset.mem_univ 2)
  rw [hγ] at h
  by_contra hh
  push Not at hh
  have : (2 : ℝ) ≤ cnt D idx Z 2 := by exact_mod_cast hh
  nlinarith [Real.pi_pos]

theorem walk_pos {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D d X Y L) :
    ∀ e ∈ L, ∃ T1 T2 : ℝ, 0 ≤ T1 ∧ 0 < T2 ∧ toV2 (e.2.1 - X) = (T1 * d.1, T1 * d.2) ∧ toV2 (Y - e.2.1) = (T2 * d.1, T2 * d.2) ∧
      (e.2.1 ≠ X → 0 < T1) := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    rcases List.mem_cons.mp he with rfl | hmem
    · obtain ⟨T, hT, hTe, hTpos⟩ := walkT_progress (WalkT.cons hS W)
      refine ⟨0, T, le_rfl, hTpos (by simp), ?_, hTe, fun h => absurd rfl h⟩
      show toV2 (X - X) = _
      ext <;> simp [toV2]
    · obtain ⟨T1, T2, h1, h2, e1, e2, e3⟩ := ih e hmem
      refine ⟨T1 + c, T2, by linarith, h2, ?_, e2, fun _ => by linarith⟩
      have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, e1, hcw]; ext <;> simp <;> ring

/-- **A non-first vertex of the walk along side `i` has corner-angle sum `π`.** -/
theorem walk_mid_asum (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) :
    ∀ e ∈ L, e.2.1 ≠ P.v i → Asum D idx e.2.1 = Real.pi := by
  intro e he hne
  obtain ⟨T1, T2, h1, h2, e1, e2, e3⟩ := walk_pos W e he
  have hT1 := e3 hne
  have hd0 : toV2 (P.e i) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  have hvert : ∃ j k, (D.tile j).pts k = e.2.1 := by
    have := walkT_mem_step W e he
    obtain ⟨kk, f, g, hk, hf, -⟩ := this
    exact ⟨e.1, kk, hk⟩
  have hc0 : P.c i e.2.1 = 0 := by
    have : P.c i e.2.1 = crs (toV2 (P.e i)) (toV2 (e.2.1 - P.v i)) := rfl
    rw [this, e1]; unfold crs; ring
  have hni : e.2.1 ∉ interior D.region := by
    rw [hreg]; exact not_interior_of_c_zero P hc0
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, -⟩ | ⟨-, hA | ⟨k, hXk, -⟩⟩
  · exact absurd hi hni
  · exact hA
  · exfalso
    by_cases hk1 : k + 1 = i
    · apply hne; rw [hXk, hk1]
    by_cases hk2 : k + 1 = i + 1
    · have hY : e.2.1 = P.v (i + 1) := by rw [hXk, hk2]
      have : toV2 (P.v (i + 1) - e.2.1) = (0, 0) := by rw [hY]; ext <;> simp [toV2]
      rw [e2] at this
      have h0 : T2 * (toV2 (P.e i)).1 = 0 := congrArg Prod.fst this
      have h0' : T2 * (toV2 (P.e i)).2 = 0 := congrArg Prod.snd this
      apply hd0
      have hT2 : T2 ≠ 0 := h2.ne'
      ext
      · exact (mul_eq_zero.mp h0).resolve_left hT2
      · exact (mul_eq_zero.mp h0').resolve_left hT2
    · have := P.c_vertex_pos hk1 hk2
      rw [← hXk] at this
      linarith

theorem steps_tile_ne (D : RegionDissection N) {d : V2} {i : Fin N} {X X' X'' : Plane} (h1 : TriStep (D.tile i) d X X') (h2 : TriStep (D.tile i) d X' X'') : False := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h1
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := h2
  have hkf : kk2 = f := (D.tile i).indep.injective (hk2.trans hf.symm)
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  obtain ⟨c', hc', hcw'⟩ := hpar2.smul
  have hsum : toV2 (X'' - X) = ((c + c') * (d.1), (c + c') * (d.2)) := by
    have : toV2 (X'' - X) = ((toV2 (X'' - X')).1 + (toV2 (X' - X)).1, (toV2 (X'' - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hcw, hcw']; ext <;> simp <;> ring
  by_cases hf2k : f2 = kk
  · have hXX : X'' = X := by rw [← hf2, hf2k, hk]
    rw [hXX] at hsum
    have hz : toV2 (X - X) = (0, 0) := by ext <;> simp [toV2]
    rw [hz] at hsum
    have h0 : (0 : ℝ) = (c + c') * d.1 := congrArg Prod.fst hsum
    have h0' : (0 : ℝ) = (c + c') * d.2 := congrArg Prod.snd hsum
    have hne : c + c' ≠ 0 := by positivity
    apply hpar.ne_right
    ext
    · exact (mul_eq_zero.mp h0.symm).resolve_left hne
    · exact (mul_eq_zero.mp h0'.symm).resolve_left hne
  · have hfin : ∀ a f g y : Fin 3, f ≠ a → g ≠ a → g ≠ f → y ≠ f → y ≠ a → g = y := by
      intro a f g y
      fin_cases a <;> fin_cases f <;> fin_cases g <;> fin_cases y <;> simp
    have hg : g = f2 := hfin kk f g f2 hfk hgk hgf (by rw [← hkf]; exact hfk2) hf2k
    have hcr : crs d (toV2 ((D.tile i).pts g - X)) = 0 := by
      rw [hg, hf2, hsum]; unfold crs; ring
    linarith

theorem walk_tail_ne {D : RegionDissection N} {d : V2} {i : Fin N} {X X' Y : Plane} {L' : List (Fin N × Plane × Plane)}
    (hS : TriStep (D.tile i) d X X') (W' : WalkT D d X' Y L') : ∀ e ∈ L', e.2.1 ≠ X := by
  intro e he h
  obtain ⟨T1, T2, h1, h2, e1, e2, e3⟩ := walk_pos W' e he
  obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hsum : toV2 (e.2.1 - X) = ((T1 + c) * d.1, (T1 + c) * d.2) := by
    have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, e1, hcw]; ext <;> simp <;> ring
  rw [h] at hsum
  have hz : toV2 (X - X) = (0, 0) := by ext <;> simp [toV2]
  rw [hz] at hsum
  have h0 : (0 : ℝ) = (T1 + c) * d.1 := congrArg Prod.fst hsum
  have h0' : (0 : ℝ) = (T1 + c) * d.2 := congrArg Prod.snd hsum
  have hne : T1 + c ≠ 0 := by positivity
  apply hpar.ne_right
  ext
  · exact (mul_eq_zero.mp h0.symm).resolve_left hne
  · exact (mul_eq_zero.mp h0'.symm).resolve_left hne

theorem walk_gamma_first (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection d X Y L)
    (hnc : ∀ e ∈ L, dist e.2.1 e.2.2 ≠ slen D 2) (hY : ∀ j, ¬ GamAt D idx j Y)
    (hmid : ∀ e ∈ L, e.2.1 ≠ X → cnt D idx e.2.1 2 ≤ 1) :
    ∀ e0, L.head? = some e0 → GamAt D idx e0.1 X := by
  induction W with
  | nil X => intro e0 he0; simp at he0
  | @cons i X X' Y L' hS W' ih =>
    intro e0 he0
    simp only [List.head?_cons, Option.some.injEq] at he0
    subst he0
    have hnc0 : dist X X' ≠ slen D 2 := hnc (i, X, X') List.mem_cons_self
    rcases step_gamma D idx hidx hS hnc0 with hX | hX'
    · exact hX
    · exfalso
      have htail := walk_tail_ne hS W'
      cases L' with
      | nil =>
        cases W'
        exact hY i hX'
      | cons e' L'' =>
        obtain ⟨i', U, V⟩ := e'
        have ih' := ih (fun e he => hnc e (List.mem_cons_of_mem _ he)) hY
          (fun e he hne => hmid e (List.mem_cons_of_mem _ he) (htail e he)) (i', U, V) rfl
        have hUX : U = X' := by
          cases W' <;> rfl
        subst hUX
        have hS' : TriStep (D.tile i') d U V := walkT_mem_step W' (i', U, V) List.mem_cons_self
        have hne : i ≠ i' := by
          intro h
          rw [h] at hS
          exact steps_tile_ne D.toRegionDissection hS hS'
        have h2 := two_tiles_two_gamma D idx hne hX' ih'
        have h3 := hmid (i', U, V) (List.mem_cons_of_mem _ List.mem_cons_self) (htail (i', U, V) List.mem_cons_self)
        simp only at h3
        omega

/-- **Every side of the polygon has a tile edge of length `c`** (Beeson-Zhang, proof of Lemma 3.4), provided no polygon vertex carries a gamma corner. -/
theorem side_has_c (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (hγ : D.model.angleAt 2 = 2 * Real.pi / 3)
    (hcorn : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0) (i : Fin M)
    {L : List (Fin N × Plane × Plane)} (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) (e0 : Fin N × Plane × Plane) (he0 : L.head? = some e0) :
    ∃ e ∈ L, dist e.2.1 e.2.2 = slen D 2 := by
  by_contra hno
  push Not at hno
  have hY : ∀ j, ¬ GamAt D idx j (P.v (i + 1)) := by
    intro j hj
    have := gamAt_cnt D idx hj
    have := hcorn i
    omega
  have hmid : ∀ e ∈ L, e.2.1 ≠ P.v i → cnt D idx e.2.1 2 ≤ 1 := by
    intro e he hne
    exact cnt_gamma_le_one D idx hγ (walk_mid_asum D P hreg idx hidxA i W e he hne)
  have := walk_gamma_first D idx hidx W hno hY hmid e0 he0
  have h1 := gamAt_cnt D idx this
  have hk : i - 1 + 1 = i := (ConvPoly.fin_facts P.three_le i).2.2.2.2.1
  have h2 := hcorn (i - 1)
  rw [hk] at h2
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.side_has_c
