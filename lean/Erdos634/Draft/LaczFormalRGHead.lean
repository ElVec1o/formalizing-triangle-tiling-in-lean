-- Draft/LaczFormalRGHead.lean -- S3 of PLAN_THM21: port of LaczFormalGraphHead to `RegionDissection` (dissection-dependent declarations only; the rest is used
-- from the original module).  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang; port of the project's LaczFormalGraphHead.
import Erdos634.Draft.LaczFormalRGGa
import Erdos634.Draft.LaczFormalGraphHead

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}


theorem walkT_split {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {P : List (Fin N × Plane × Plane)} {e : Fin N × Plane × Plane} {Q : List (Fin N × Plane × Plane)}
    (h : L = P ++ e :: Q) : WalkT D d X e.2.1 P ∧ WalkT D d e.2.1 Y (e :: Q) := by
  induction P generalizing X L with
  | nil =>
    simp only [List.nil_append] at h
    subst h
    cases W with
    | cons hS W' => exact ⟨WalkT.nil _, WalkT.cons hS W'⟩
  | cons x P ih =>
    simp only [List.cons_append] at h
    subst h
    cases W with
    | cons hS W' =>
      obtain ⟨h1, h2⟩ := ih W' rfl
      exact ⟨WalkT.cons hS h1, h2⟩


theorem walkR_split {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) {P : List (Fin N × Plane × Plane)} {e : Fin N × Plane × Plane} {Q : List (Fin N × Plane × Plane)}
    (h : L = P ++ e :: Q) : WalkR D d X e.2.1 P ∧ WalkR D d e.2.1 Y (e :: Q) := by
  induction P generalizing X L with
  | nil =>
    simp only [List.nil_append] at h
    subst h
    cases W with
    | cons hS W' => exact ⟨WalkR.nil _, WalkR.cons hS W'⟩
  | cons x P ih =>
    simp only [List.cons_append] at h
    subst h
    cases W with
    | cons hS W' =>
      obtain ⟨h1, h2⟩ := ih W' rfl
      exact ⟨WalkR.cons hS h1, h2⟩


/-- Two divisions with the same total, one all `a`, the other starting with a non-`a`. -/
theorem abc_contra (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} {X Y : Plane}
    {P1 : List (Fin N × Plane × Plane)} {P2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d X Y P1) (W2 : WalkR D.toRegionDissection d X Y P2)
    (hall : ∀ e ∈ P1, dist e.2.1 e.2.2 = slen D 0) {e2 : Fin N × Plane × Plane} {P2' : List (Fin N × Plane × Plane)}
    (h2 : P2 = e2 :: P2') (hf2 : dist e2.2.1 e2.2.2 ≠ slen D 0) : False := by
  refine abc_core (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) hnc (P1.map fun e => dist e.2.1 e.2.2)
    (P2.map fun e => dist e.2.1 e.2.2) ?_ ?_ ?_ ⟨dist e2.2.1 e2.2.2, ?_, hf2⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hall e he
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have := side_len_mem D idx hidx (walkR_mem_step W2 e he)
    rw [dist_comm] at this
    exact this
  · rw [walkT_dist_sum W1, walkR_dist_sum W2]
  · exact List.mem_map.mpr ⟨e2, by rw [h2]; exact List.mem_cons_self .., rfl⟩


/-- The mirror: right division all `a`, left division starting with a non-`a`. -/
theorem abc_contra' (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} {X Y : Plane}
    {P1 : List (Fin N × Plane × Plane)} {P2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d X Y P1) (W2 : WalkR D.toRegionDissection d X Y P2)
    (hall : ∀ e ∈ P2, dist e.2.1 e.2.2 = slen D 0) {e1 : Fin N × Plane × Plane} {P1' : List (Fin N × Plane × Plane)}
    (h1 : P1 = e1 :: P1') (hf1 : dist e1.2.1 e1.2.2 ≠ slen D 0) : False := by
  refine abc_core (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) hnc (P2.map fun e => dist e.2.1 e.2.2)
    (P1.map fun e => dist e.2.1 e.2.2) ?_ ?_ ?_ ⟨dist e1.2.1 e1.2.2, ?_, hf1⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hall e he
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem D idx hidx (walkT_mem_step W1 e he)
  · rw [walkT_dist_sum W1, walkR_dist_sum W2]
  · exact List.mem_map.mpr ⟨e1, by rw [h1]; exact List.mem_cons_self .., rfl⟩


/-- **Structure at the head (left case).** -/
theorem ga_head_left (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L1 H) (hR2 : ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ slen D 0) :
    ∃ (iA : Fin N) (HA : Plane) (iB : Fin N) (HB : Plane) (iS : Fin N) (V V' : Plane) (σ : ℝ),
      TriStep (D.tile iA) d HA H ∧ dist HA H = slen D 0 ∧ TriStep (D.tile iB) d H HB ∧ dist H HB ≠ slen D 0 ∧
      TriStep (D.tile iS) (neg2 d) V' V ∧ 0 < σ ∧ σ < 1 ∧ H = V + σ • (V' - V) ∧ H ≠ X := by
  classical
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot, hH⟩ := hRun
  obtain ⟨hpre, hsuf⟩ := walkT_split W1 hdec
  subst hH
  -- (A): the last step of the prefix
  obtain ⟨iA, HA, hmemA, hSA⟩ := walkT_last hpre hL'ne
  have hdA : dist HA e0.2.1 = slen D 0 := hall (iA, HA, e0.2.1) hmemA
  -- (B): the step `e0`
  have hmem0 : e0 ∈ L1 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hSB := walkT_mem_step W1 e0 hmem0
  -- parameters
  obtain ⟨tH, htH, htHe, htHp⟩ := walkT_progress hpre
  have htHpos := htHp hL'ne
  obtain ⟨T', hT', hT'e, hT'p⟩ := walkT_progress hsuf
  have hT'pos := hT'p (by simp)
  have hXY : toV2 (Y - X) = ((tH + T') * d.1, (tH + T') * d.2) := by
    have : toV2 (Y - X) = ((toV2 (Y - e0.2.1)).1 + (toV2 (e0.2.1 - X)).1, (toV2 (Y - e0.2.1)).2 + (toV2 (e0.2.1 - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hT'e, htHe]; ext <;> simp <;> ring
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover W2 hXY hd tH htH (by linarith)
  have hSe := walkR_mem_step W2 e he
  have hHX : e0.2.1 ≠ X := by
    intro h
    rw [h] at htHe
    have h1' : tH * d.1 = 0 := by have := congrArg Prod.fst htHe; simpa [toV2] using this.symm
    have h2' : tH * d.2 = 0 := by have := congrArg Prod.snd htHe; simpa [toV2] using this.symm
    exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left htHpos.ne') ((mul_eq_zero.mp h2').resolve_left htHpos.ne'))
  -- `H` is not the tail of the right step `e`
  have hne0 : t0 ≠ tH := by
    intro hteq
    have hc0 := coords_of_toV2 h0
    have hcH := coords_of_toV2 htHe
    have heH : e.2.1 = e0.2.1 := by
      apply pt_ext
      · rw [hc0.1, hcH.1, hteq]
      · rw [hc0.2, hcH.2, hteq]
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem he
    obtain ⟨hpreR, -⟩ := walkR_split W2 hPQ
    rw [heH] at hpreR
    have hPne : P ≠ [] := by
      rintro rfl
      cases hpreR
      exact hHX rfl
    obtain ⟨p1, P', hP1⟩ := List.exists_cons_of_ne_nil hPne
    have hhead : dist p1.2.1 p1.2.2 ≠ slen D 0 := by
      apply hR2 p1
      rw [hPQ, hP1]; simp
    exact abc_contra D idx hidx hnc hpre hpreR hall hP1 hhead
  have hlt0 : t0 < tH := lt_of_le_of_ne h2 hne0
  have hlt01 : t0 < t1 := lt_trans hlt0 h3
  set σ : ℝ := (tH - t0) / (t1 - t0) with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (by linarith)
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have hσm : σ * (t1 - t0) = tH - t0 := by
    have hne : t1 - t0 ≠ 0 := by linarith
    rw [hσ]; exact div_mul_cancel₀ _ hne
  refine ⟨iA, HA, e0.1, e0.2.2, e.1, e.2.1, e.2.2, σ, hSA, hdA, hSB, hnot, hSe, hσ0, hσ1, ?_, hHX⟩
  have d0 := coords_of_toV2 h0
  have d1 := coords_of_toV2 h1
  have cH := coords_of_toV2 htHe
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.2, d0.2, d1.2]; linear_combination (-d.2) * hσm


/-- **Structure at the head (right case)**: mirror of `ga_head_left`. -/
theorem ga_head_right (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L2 H) (hL1 : ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ slen D 0) :
    ∃ (iA : Fin N) (HA : Plane) (iB : Fin N) (HB : Plane) (iS : Fin N) (V V' : Plane) (σ : ℝ),
      TriStep (D.tile iA) (neg2 d) H HA ∧ dist HA H = slen D 0 ∧ TriStep (D.tile iB) (neg2 d) HB H ∧ dist H HB ≠ slen D 0 ∧
      TriStep (D.tile iS) d V V' ∧ 0 < σ ∧ σ < 1 ∧ H = V + σ • (V' - V) ∧ H ≠ X := by
  classical
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot, hH⟩ := hRun
  obtain ⟨hpre, hsuf⟩ := walkR_split W2 hdec
  subst hH
  obtain ⟨iA, HA, hmemA, hSA⟩ := walkR_last hpre hL'ne
  have hdA : dist HA e0.2.1 = slen D 0 := hall (iA, HA, e0.2.1) hmemA
  have hmem0 : e0 ∈ L2 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hSB := walkR_mem_step W2 e0 hmem0
  obtain ⟨tH, htH, htHe, htHp⟩ := walkR_progress hpre
  have htHpos := htHp hL'ne
  obtain ⟨T', hT', hT'e, hT'p⟩ := walkR_progress hsuf
  have hT'pos := hT'p (by simp)
  have hXY : toV2 (Y - X) = ((tH + T') * d.1, (tH + T') * d.2) := by
    have : toV2 (Y - X) = ((toV2 (Y - e0.2.1)).1 + (toV2 (e0.2.1 - X)).1, (toV2 (Y - e0.2.1)).2 + (toV2 (e0.2.1 - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hT'e, htHe]; ext <;> simp <;> ring
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover W1 hXY hd tH htH (by linarith)
  have hSe := walkT_mem_step W1 e he
  have hHX : e0.2.1 ≠ X := by
    intro h
    rw [h] at htHe
    have h1' : tH * d.1 = 0 := by have := congrArg Prod.fst htHe; simpa [toV2] using this.symm
    have h2' : tH * d.2 = 0 := by have := congrArg Prod.snd htHe; simpa [toV2] using this.symm
    exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left htHpos.ne') ((mul_eq_zero.mp h2').resolve_left htHpos.ne'))
  have hne0 : t0 ≠ tH := by
    intro hteq
    have hc0 := coords_of_toV2 h0
    have hcH := coords_of_toV2 htHe
    have heH : e.2.1 = e0.2.1 := by
      apply pt_ext
      · rw [hc0.1, hcH.1, hteq]
      · rw [hc0.2, hcH.2, hteq]
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem he
    obtain ⟨hpreT, -⟩ := walkT_split W1 hPQ
    rw [heH] at hpreT
    have hPne : P ≠ [] := by
      rintro rfl
      cases hpreT
      exact hHX rfl
    obtain ⟨p1, P', hP1⟩ := List.exists_cons_of_ne_nil hPne
    have hhead : dist p1.2.1 p1.2.2 ≠ slen D 0 := by
      apply hL1 p1
      rw [hPQ, hP1]; simp
    exact abc_contra' D idx hidx hnc hpreT hpre hall hP1 hhead
  have hlt0 : t0 < tH := lt_of_le_of_ne h2 hne0
  have hlt01 : t0 < t1 := lt_trans hlt0 h3
  set σ : ℝ := (tH - t0) / (t1 - t0) with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (by linarith)
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have hσm : σ * (t1 - t0) = tH - t0 := by
    have hne : t1 - t0 ≠ 0 := by linarith
    rw [hσ]; exact div_mul_cancel₀ _ hne
  refine ⟨iA, HA, e0.1, e0.2.2, e.1, e.2.1, e.2.2, σ, hSA, hdA, hSB, hnot, hSe, hσ0, hσ1, ?_, hHX⟩
  have d0 := coords_of_toV2 h0
  have d1 := coords_of_toV2 h1
  have cH := coords_of_toV2 htHe
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.2, d0.2, d1.2]; linear_combination (-d.2) * hσm


/-- **An edge of `Γ_a` starts at `X` from local data (right version)**: the right first side has length `a` and the left first side does not. -/
theorem ga_edge_of_local' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X : Plane}
    (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toRegionDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 ≠ slen D 0)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X = slen D 0) :
    ∃ H, GaEdge D.toRegionDissection (slen D 0) X H := by
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd hX ⟨i1, U1, hl⟩ ⟨i2, U2, hr⟩
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
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr
  have hd1 : dist e1.2.1 e1.2.2 ≠ slen D 0 := by rw [he1X, hU1]; exact hla
  have hd2 : dist e2.2.1 e2.2.2 = slen D 0 := by
    rw [he2X, hU2, dist_comm]; exact hra
  have hex : ∃ e ∈ L2, dist e.2.1 e.2.2 ≠ slen D 0 := by
    by_contra hall
    push_neg at hall
    exact abc_contra' D idx hidx hnc W1 W2 hall hL1e hd1
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot⟩ := list_first_not (fun x : Fin N × Plane × Plane => dist x.2.1 x.2.2 = slen D 0) L2
    (by rw [hL2e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hd2)
    hL2 hex
  refine ⟨e0.2.1, d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, Or.inr ⟨⟨L', e0, L'', hdec, hL'ne, hall, hnot, rfl⟩, ?_⟩⟩
  intro x hx
  rw [hL1e] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx]; exact hd1


/-- **An edge of `Γ_a` along a ray of the fan** between two adjacent corner sectors `x` (clockwise) and `y` (counterclockwise): if `NoBack` holds and exactly one of the two first
sides has length `a`, `Γ_a` has an edge out of `H`. -/
theorem ga_edge_of_ray (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hcx : 0 < crs (F.p x) (F.q x)) (hcy : 0 < crs (F.p y) (F.q y))
    (hxy : Par (F.p y) (F.q x)) (hnb : NoBack D.toRegionDissection (F.q x) H)
    (hxor : (nsq (F.q x) = slen D 0 ^ 2 ∧ nsq (F.p y) ≠ slen D 0 ^ 2) ∨
            (nsq (F.q x) ≠ slen D 0 ^ 2 ∧ nsq (F.p y) = slen D 0 ^ 2)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hd : F.q x ≠ 0 := (F.hok x).ne_q
  have hcornx : ∃ k, (D.tile x.1).pts k = H := by
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcx; unfold crs at hcx; try simp only at hcx; nlinarith
  have horny : ∃ k, (D.tile y.1).pts k = H := by
    rcases F.hspec y with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcy; unfold crs at hcy; try simp only at hcy; nlinarith
  obtain ⟨kx, flx, hkx, hpx, hqx⟩ := spec_corner_data (F.hspec x) hcornx
  obtain ⟨ky, fly, hky, hpy, hqy⟩ := spec_corner_data (F.hspec y) horny
  have hstepR := triStep_of_end (T := D.tile x.1) (d := F.q x) kx flx hkx hpx hqx hcx (par_refl hd)
  have hstepL := triStep_of_start (T := D.tile y.1) (d := F.q x) ky fly hky hpy hqy hcy hxy
  have hX : ∃ j k, (D.tile j).pts k = H := ⟨y.1, ky, hky⟩
  have hdL : dist H ((D.tile y.1).pts (armP ky fly)) ^ 2 = nsq (F.p y) := by
    rw [hpy, nsq_toV2_sub, dist_comm]
  have hdR : dist ((D.tile x.1).pts (armQ kx flx)) H ^ 2 = nsq (F.q x) := by
    rw [hqx, nsq_toV2_sub]
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the right first side is `a`: right version
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H = slen D 0 := by
      have := hdR.trans h1
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hla : dist H ((D.tile y.1).pts (armP ky fly)) ≠ slen D 0 := by
      intro h; apply h2; rw [← hdL, h]
    exact ga_edge_of_local' D idx hidx hnc hd hX hnb hstepL hla hstepR hra
  · have hla : dist H ((D.tile y.1).pts (armP ky fly)) = slen D 0 := by
      have := hdL.trans h2
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H ≠ slen D 0 := by
      intro h; apply h1; rw [← hdR, h]
    exact ga_edge_of_local D idx hidx hnc hd hX hnb hstepL hla hstepR hra


end Erdos634.Draft.LaczFormal.RG
