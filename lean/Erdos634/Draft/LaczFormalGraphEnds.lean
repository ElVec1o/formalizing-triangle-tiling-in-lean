-- Draft/LaczFormalGraphEnds.lean -- D1 (part 2): the two divisions of a maximal segment end at the SAME point.
-- Left walk (`WalkT D d`, left tiles along `d` from `X`) and right walk (`WalkR D d`, right tiles along `d` from `X`): if both are nonempty and neither can be
-- continued (`no left step from Y1`, `no right step from Y2`), then `Y1 = Y2`.  Proof by the ray principle (`ExtFan.ray_left/right`) at the earlier
-- end point.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4: "divisions X = U_0, .., U_k = Y and X = V_0, .., V_l = Y of the segment XY").
import Erdos634.Draft.LaczFormalGraphExt

open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- The reversed direction. -/
def neg2 (d : V2) : V2 := (-d.1, -d.2)

/-- A chain of right steps along `d` (tail `X`, head `X'` further along `d`; the tile lies to the right of `d`). -/
inductive WalkR (D : Dissection N) (d : V2) : Plane → Plane → List (Fin N × Plane × Plane) → Prop
  | nil (X : Plane) : WalkR D d X X []
  | cons {i : Fin N} {X X' Y : Plane} {L : List (Fin N × Plane × Plane)} :
      TriStep (D.tile i) (neg2 d) X' X → WalkR D d X' Y L → WalkR D d X Y ((i, X, X') :: L)

theorem walkR_progress {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) : ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ (L ≠ [] → 0 < T) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by unfold toV2; ext <;> simp, fun h => absurd rfl h⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS
    -- hpar : Par (toV2 (X - X')) (neg2 d)
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun _ => by positivity⟩
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hTe, h1]
    ext <;> simp <;> ring

/-- Covering lemma, left walk: every parameter `s` in `[0, T)` lies in `[t0, t1)` of some step. -/
theorem walkT_cover {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 ≤ s → s < T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 ≤ s ∧ s < t1 := by
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
    by_cases hsc : s < c
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

/-- Covering lemma, right walk. -/
theorem walkR_cover {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 ≤ s → s < T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 ≤ s ∧ s < t1 := by
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
    by_cases hsc : s < c
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

theorem walkT_last {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) (hL : L ≠ []) : ∃ i U, (i, U, Y) ∈ L ∧ TriStep (D.tile i) d U Y := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      cases W
      exact ⟨i, X, List.mem_cons_self .., hS⟩
    · obtain ⟨j, U, hmem, hSj⟩ := ih hL'
      exact ⟨j, U, List.mem_cons_of_mem _ hmem, hSj⟩

theorem walkR_last {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) (hL : L ≠ []) : ∃ i U, (i, U, Y) ∈ L ∧ TriStep (D.tile i) (neg2 d) Y U := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      cases W
      exact ⟨i, X, List.mem_cons_self .., hS⟩
    · obtain ⟨j, U, hmem, hSj⟩ := ih hL'
      exact ⟨j, U, List.mem_cons_of_mem _ hmem, hSj⟩

theorem walkR_mem_step {D : Dissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) : ∀ e ∈ L, TriStep (D.tile e.1) (neg2 d) e.2.2 e.2.1 := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact hS
    · exact ih e h

/-- A corner sector whose counterclockwise ray points along `d` gives a step along `-d`. -/
theorem triStep_of_end {T : Tri} {d : V2} {U : Plane} (kk : Fin 3) (fl : Bool) (hk : T.pts kk = U) {p q : V2}
    (hp : p = toV2 (T.pts (armP kk fl) - U)) (hq : q = toV2 (T.pts (armQ kk fl) - U))
    (hcrs : 0 < crs p q) (hpar : Par q d) : TriStep T (neg2 d) (T.pts (armQ kk fl)) U := by
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  refine ⟨armQ kk fl, kk, armP kk fl, rfl, hk, (armQ_ne kk fl).symm, (armPQ_ne kk fl), (armP_ne kk fl), ?_, ?_⟩
  · have : toV2 (U - T.pts (armQ kk fl)) = (-q.1, -q.2) := by
      rw [hq]; unfold toV2; ext <;> simp
    rw [this]
    exact par_neg hpar
  · have e1 : toV2 (T.pts (armP kk fl) - T.pts (armQ kk fl)) = (p.1 - q.1, p.2 - q.2) := by
      rw [hp, hq]; unfold toV2; ext <;> simp [← hk]
    rw [e1]
    have h1 : crs p q = c * crs p d := by rw [hcq]; unfold crs; ring
    rw [h1] at hcrs
    have hpd : 0 < crs p d := (mul_pos_iff_of_pos_left hc).mp hcrs
    unfold crs at hpd
    unfold crs neg2
    try simp only at hpd ⊢
    rw [hcq]
    nlinarith [hpd]

/-- **Interior points of a step.**  Points strictly between the ends of a step's side lie in the tile, are not vertices of it, and lie on the line. -/
theorem step_interior_pt {T : Tri} {d : V2} {A B : Plane} (hS : TriStep T d A B) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    A + σ • (B - A) ∈ T.carrier ∧ (∀ k, T.pts k ≠ A + σ • (B - A)) ∧ crs d (toV2 (A + σ • (B - A) - A)) = 0 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hAB : B ≠ A := by
    intro h; apply hfk; apply T.indep.injective; rw [hf, hk]; exact h
  have hAm : A ∈ T.carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hBm : B ∈ T.carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  have hY : toV2 (A + σ • (B - A) - A) = (σ * (c * d.1), σ * (c * d.2)) := by
    have : toV2 (A + σ • (B - A) - A) = (σ * (toV2 (B - A)).1, σ * (toV2 (B - A)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hcw]
  refine ⟨T.convex.add_smul_sub_mem hAm hBm ⟨h0.le, h1.le⟩, ?_, ?_⟩
  · intro k hkY
    rcases fin3_three kk f g hfk hgk hgf k with rfl | rfl | rfl
    · rw [hk] at hkY
      have : σ • (B - A) = 0 := by simpa using hkY.symm
      rcases smul_eq_zero.mp this with h | h
      · linarith
      · exact hAB (sub_eq_zero.mp h)
    · rw [hf] at hkY
      have h2 : (σ - 1) • (B - A) = 0 := by
        have : A + σ • (B - A) - B = 0 := by rw [← hkY]; simp
        rw [sub_smul, one_smul]
        calc σ • (B - A) - (B - A) = A + σ • (B - A) - B := by abel
          _ = 0 := this
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact hAB (sub_eq_zero.mp h)
    · have hline := hY
      have hg : crs d (toV2 (T.pts k - A)) > 0 := hleft
      rw [hkY, hY] at hg
      unfold crs at hg; try simp only at hg; nlinarith
  · rw [hY]; unfold crs; ring

/-- The sector of a tile at an interior point of one of its sides along `d'` is straight, with clockwise ray along `d'`. -/
theorem straight_dir {D : Dissection N} {V : Plane} (b : AtV D V) {p q : V2} (hok : SecOK p q)
    (hloc : LocalCone (D.tile b.1) V p q) (hspec : SectorSpec (D.tile b.1) V p q)
    (hnv : ∀ k, (D.tile b.1).pts k ≠ V) {d' : V2} {A B : Plane} (hS : TriStep (D.tile b.1) d' A B)
    (hline : crs d' (toV2 (V - A)) = 0) : Par p d' ∧ q = (-p.1, -p.2) := by
  rcases hspec with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
  · exact absurd hk (hnv k)
  · subst hq
    exact ⟨pT_par_d hS hline hok.ne_p hloc, rfl⟩

theorem coords_of_toV2 {P X : Plane} {t : ℝ} {d : V2} (h : toV2 (P - X) = (t * d.1, t * d.2)) :
    P 0 = X 0 + t * d.1 ∧ P 1 = X 1 + t * d.2 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [toV2] at h1 h2
  simp only [PiLp.sub_apply] at h1 h2
  constructor <;> linarith

theorem pt_ext {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem neg2_neg2 (d : V2) : ((-(neg2 d).1, -(neg2 d).2) : V2) = d := by
  unfold neg2; ext <;> simp

/-- **The two divisions end together.** -/
theorem ends_coincide (D : Dissection N) {d : V2} (hd : d ≠ 0) {X Y1 Y2 : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (hL1 : L1 ≠ []) (hL2 : L2 ≠ [])
    (W1 : WalkT D d X Y1 L1) (W2 : WalkR D d X Y2 L2)
    (hno1 : ∀ i U', ¬ TriStep (D.tile i) d Y1 U') (hno2 : ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y2) : Y1 = Y2 := by
  classical
  obtain ⟨T1, hT1, hT1e, hT1p⟩ := walkT_progress W1
  obtain ⟨T2, hT2, hT2e, hT2p⟩ := walkR_progress W2
  have p1 := hT1p hL1
  have p2 := hT2p hL2
  have c1 := coords_of_toV2 hT1e
  have c2 := coords_of_toV2 hT2e
  have hTeq : T1 = T2 := by
    rcases lt_trichotomy T1 T2 with hlt | heq | hgt
    · -- the right walk runs past the end of the left walk
      exfalso
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover W2 hT2e hd T1 hT1 hlt
      have hSe := walkR_mem_step W2 e he
      obtain ⟨i1, U1, hmem1, hS1⟩ := walkT_last W1 hL1
      obtain ⟨kkL, fL, gL, hkL, hfL, -⟩ := id hS1
      have hvert : ∃ j k, (D.tile j).pts k = Y1 := ⟨i1, fL, hfL⟩
      obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D Y1 hvert
      have hmemA : Y1 ∈ (D.tile i1).carrier := hfL ▸ subset_convexHull ℝ _ ⟨fL, rfl⟩
      set a : AtV D Y1 := ⟨i1, hmemA⟩ with ha
      obtain ⟨kk', fl', hk', hpa, hqa⟩ := spec_corner_data (F.hspec a) ⟨fL, hfL⟩
      have hqa' : Par (F.q a) (-d.1, -d.2) := triStep_end hS1 kk' fl' hk' hpa hqa (F.hok a)
      have hcrsA : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
      -- the right tile `e` covers Y1
      have hlt01 : t0 < t1 := lt_of_le_of_lt h2 h3
      set σ : ℝ := (T1 - t0) / (t1 - t0) with hσ
      have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
      have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
      have hσm : σ * (t1 - t0) = T1 - t0 := by
        have hne : t1 - t0 ≠ 0 := by linarith
        rw [hσ]; exact div_mul_cancel₀ _ hne
      have hY1 : Y1 = e.2.1 + σ • (e.2.2 - e.2.1) := by
        have d0 := coords_of_toV2 h0
        have d1 := coords_of_toV2 h1
        apply pt_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c1.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c1.2, d0.2, d1.2]; linear_combination (-d.2) * hσm
      have hqb : ∃ b : AtV D Y1, Par (F.q b) d := by
        obtain ⟨kkS, fS, gS, hkS, hfS, hfkS, hgkS, hgfS, hparS, hleftS⟩ := id hSe
        rcases hσ0.eq_or_lt with h00 | hpos
        · -- Y1 is the head vertex of the step
          have hY1e : Y1 = e.2.1 := by rw [hY1, ← h00]; simp
          subst hY1e
          have hmemb : e.2.1 ∈ (D.tile e.1).carrier := by rw [← hfS]; exact subset_convexHull ℝ _ ⟨fS, rfl⟩
          set b : AtV D e.2.1 := ⟨e.1, hmemb⟩
          obtain ⟨kk2, fl2, hk2, hpb, hqb'⟩ := spec_corner_data (F.hspec b) ⟨fS, hfS⟩
          have := triStep_end hSe kk2 fl2 hk2 hpb hqb' (F.hok b)
          exact ⟨b, by rw [neg2_neg2] at this; exact this⟩
        · -- interior point of the side
          have hσ1' : 0 < 1 - σ := by linarith
          have hσ2' : 1 - σ < 1 := by linarith
          obtain ⟨hmemb, hnv, hline⟩ := step_interior_pt hSe hσ1' hσ2'
          have hYe : e.2.2 + (1 - σ) • (e.2.1 - e.2.2) = Y1 := by
            rw [hY1]; ext i; simp; ring
          rw [hYe] at hmemb hnv hline
          set b : AtV D Y1 := ⟨e.1, hmemb⟩
          obtain ⟨hpar, hq⟩ := straight_dir b (F.hok b) (F.hloc b) (F.hspec b) hnv hSe hline
          refine ⟨b, ?_⟩
          rw [hq]
          have := par_neg hpar
          rw [neg2_neg2] at this
          exact this
      obtain ⟨b, hb⟩ := hqb
      obtain ⟨c, hcrs, hcp⟩ := F.ray_left a b hcrsA hqa' hb
      have hcorner : ∃ k, (D.tile c.1).pts k = Y1 := by
        rcases F.hspec c with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
        · exact ⟨k, hk⟩
        · exfalso
          rw [hq] at hcrs
          unfold crs at hcrs; simp only at hcrs; nlinarith
      obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec c) hcorner
      exact hno1 c.1 _ (triStep_of_start kk3 fl3 hk3 hp3 hq3 hcrs hcp)
    · exact heq
    · -- the left walk runs past the end of the right walk
      exfalso
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover W1 hT1e hd T2 hT2 hgt
      have hSe := walkT_mem_step W1 e he
      obtain ⟨i2, U2, hmem2, hS2⟩ := walkR_last W2 hL2
      obtain ⟨kkR, fR, gR, hkR, hfR, -⟩ := id hS2
      have hvert : ∃ j k, (D.tile j).pts k = Y2 := ⟨i2, kkR, hkR⟩
      obtain ⟨κ, _, ⟨F⟩⟩ := extFan_exists D Y2 hvert
      have hmemA : Y2 ∈ (D.tile i2).carrier := hkR ▸ subset_convexHull ℝ _ ⟨kkR, rfl⟩
      set a : AtV D Y2 := ⟨i2, hmemA⟩ with ha
      obtain ⟨kk', fl', hk', hpa, hqa⟩ := spec_corner_data (F.hspec a) ⟨kkR, hkR⟩
      have hpa' : Par (F.p a) (neg2 d) := triStep_start hS2 kk' fl' hk' hpa hqa (F.hok a)
      have hcrsA : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
      have hlt01 : t0 < t1 := lt_of_le_of_lt h2 h3
      set σ : ℝ := (T2 - t0) / (t1 - t0) with hσ
      have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
      have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
      have hσm : σ * (t1 - t0) = T2 - t0 := by
        have hne : t1 - t0 ≠ 0 := by linarith
        rw [hσ]; exact div_mul_cancel₀ _ hne
      have hY2 : Y2 = e.2.1 + σ • (e.2.2 - e.2.1) := by
        have d0 := coords_of_toV2 h0
        have d1 := coords_of_toV2 h1
        apply pt_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c2.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c2.2, d0.2, d1.2]; linear_combination (-d.2) * hσm
      have hpb : ∃ b : AtV D Y2, Par (F.p b) d := by
        obtain ⟨kkS, fS, gS, hkS, hfS, hfkS, hgkS, hgfS, hparS, hleftS⟩ := id hSe
        rcases hσ0.eq_or_lt with h00 | hpos
        · have hY2e : Y2 = e.2.1 := by rw [hY2, ← h00]; simp
          subst hY2e
          have hmemb : e.2.1 ∈ (D.tile e.1).carrier := by rw [← hkS]; exact subset_convexHull ℝ _ ⟨kkS, rfl⟩
          set b : AtV D e.2.1 := ⟨e.1, hmemb⟩
          obtain ⟨kk2, fl2, hk2, hpb, hqb'⟩ := spec_corner_data (F.hspec b) ⟨kkS, hkS⟩
          exact ⟨b, triStep_start hSe kk2 fl2 hk2 hpb hqb' (F.hok b)⟩
        · obtain ⟨hmemb, hnv, hline⟩ := step_interior_pt hSe hpos hσ1
          rw [← hY2] at hmemb hnv hline
          set b : AtV D Y2 := ⟨e.1, hmemb⟩
          obtain ⟨hpar, -⟩ := straight_dir b (F.hok b) (F.hloc b) (F.hspec b) hnv hSe hline
          exact ⟨b, hpar⟩
      obtain ⟨b, hb⟩ := hpb
      obtain ⟨c, hcrs, hcq⟩ := F.ray_right a b hcrsA hpa' hb
      have hcorner : ∃ k, (D.tile c.1).pts k = Y2 := by
        rcases F.hspec c with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
        · exact ⟨k, hk⟩
        · exfalso
          rw [hq] at hcrs
          unfold crs at hcrs; simp only at hcrs; nlinarith
      obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec c) hcorner
      exact hno2 c.1 _ (triStep_of_end kk3 fl3 hk3 hp3 hq3 hcrs hcq)
  have hY : Y1 = Y2 := by
    apply pt_ext
    · rw [c1.1, c2.1, hTeq]
    · rw [c1.2, c2.2, hTeq]
  exact hY

end Erdos634.Draft.LaczFormal.Graph

#print axioms Erdos634.Draft.LaczFormal.Graph.ends_coincide
#print axioms Erdos634.Draft.LaczFormal.Graph.ExtFan.ray_left
#print axioms Erdos634.Draft.LaczFormal.Graph.ExtFan.ray_right
#print axioms Erdos634.Draft.LaczFormal.Graph.extFan_exists
