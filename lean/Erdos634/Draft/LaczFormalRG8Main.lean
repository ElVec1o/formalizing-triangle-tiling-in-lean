-- Draft/LaczFormalRG8Main.lean -- Laczkovich DCG 48 (2012), Lemma 4.6 (`Gamma_c` is empty when `a, b` are commensurable and `c` is not a rational multiple of `a`),
-- polygon version, CONDITIONAL on the arrival statement `Arrival D` (an edge of `Gamma_c` that arrives at an inner point of a maximal segment starts at one of its ends).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemmas 4.5, 4.6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG8Deg

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Arrival** (Laczkovich, proof of Lemma 4.6: "an edge `ZW` arriving at an inner point `W` of a maximal segment `XY` starts at `X` or `Y`"): on a maximal segment `XY` with divisions `LA, LB`,
let `W` be an end of an element of `LB` that lies strictly inside an element of `LA`; an edge of `Gamma_c` into `W` starts at `X`, or at a point of the line of parameter `>= ` that of `Y`. -/
def Arrival (D : CongruentRegionDissection N) : Prop :=
  ∀ (d : V2) (X Y W Z : Plane) (bA : Bool) (LA LB : List (Fin N × Plane × Plane)),
    d ≠ 0 → NoBack D.toRegionDissection d X → WalkU D.toRegionDissection bA d X Y LA → WalkU D.toRegionDissection (!bA) d X Y LB →
    LA ≠ [] → LB ≠ [] → (∀ i U', ¬ TriStep (D.tile i) d Y U') → (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y) →
    (∃ f ∈ LB, f.2.2 = W) → (∃ g ∈ LA, ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ W = g.2.1 + σ • (g.2.2 - g.2.1)) → GcEdge D Z W →
    Z = X ∨ ∃ z T : ℝ, toV2 (Z - X) = (z * d.1, z * d.2) ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ T ≤ z

theorem toV2_pt {X V : Plane} {t : ℝ} {d : V2} (h : toV2 (V - X) = (t * d.1, t * d.2)) :
    toV2 V = ((toV2 X).1 + t * d.1, (toV2 X).2 + t * d.2) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [toV2_sub] at h1 h2
  simp only [toV2]
  ext <;> simp <;> linarith

theorem param_unique {d : V2} (hd : d ≠ 0) {t t' : ℝ} (h : ((t * d.1, t * d.2) : V2) = (t' * d.1, t' * d.2)) : t = t' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  by_contra hne
  apply hd
  have h3 : (t - t') * d.1 = 0 := by linarith
  have h4 : (t - t') * d.2 = 0 := by linarith
  have hs : t - t' ≠ 0 := sub_ne_zero.mpr hne
  exact Prod.ext ((mul_eq_zero.mp h3).resolve_left hs) ((mul_eq_zero.mp h4).resolve_left hs)

theorem walkU_adj {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {P1 P2 : List (Fin N × Plane × Plane)} {u1 u2 : Fin N × Plane × Plane}
    (W : WalkU D b d X Y (P1 ++ u1 :: u2 :: P2)) : u1.2.2 = u2.2.1 := by
  obtain ⟨-, h2⟩ := walkU_split W rfl
  obtain ⟨i, A, B⟩ := u1
  cases h2 with
  | cons hS W' => exact (walkU_head W').symm

/-- Extremality of `V` among the tails of edges. -/
def ExtV (D : CongruentRegionDissection N) (V : Plane) : Prop := ∀ v H, GcEdge D v H → nsq (toV2 v) ≤ nsq (toV2 V)

/-- **No transition inside the prefix**: at an end `W` of an element of the division `LB` that is not an end of `LA`, the two `LB`-elements around `W` have the same `c`-status. -/
theorem no_transition (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (Pg : ConvPoly M) (hreg : D.region = Pg.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hArr : Arrival D)
    {X Y V : Plane} {d : V2} {bA : Bool} {LA LB : List (Fin N × Plane × Plane)}
    (hd : d ≠ 0) (hnb : NoBack D.toRegionDissection d X) (wA : WalkU D.toRegionDissection bA d X Y LA) (wB : WalkU D.toRegionDissection (!bA) d X Y LB)
    (hLA : LA ≠ []) (hLB : LB ≠ []) (nc1 : ∀ i U', ¬ TriStep (D.tile i) d Y U') (nc2 : ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y)
    (hext : ExtV D V) (hEXV : GcEdge D X V) {sV T : ℝ} (hsV : 0 < sV) (hV : toV2 (V - X) = (sV * d.1, sV * d.2))
    (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hsVT : sV < T) (hVA : ∃ g ∈ LA, g.2.2 = V)
    {P1 P2 : List (Fin N × Plane × Plane)} {u1 u2 : Fin N × Plane × Plane} (hdec : LB = P1 ++ u1 :: u2 :: P2)
    (hnA : ¬ ∃ g ∈ LA, g.2.2 = u1.2.2)
    (hord : (dist u1.2.1 u1.2.2 = slen D 2 ∧ dist u2.2.1 u2.2.2 ≠ slen D 2) ∨ (dist u1.2.1 u1.2.2 ≠ slen D 2 ∧ dist u2.2.1 u2.2.2 = slen D 2)) : False := by
  classical
  set W := u1.2.2 with hW
  have hadj : u1.2.2 = u2.2.1 := walkU_adj (hdec ▸ wB)
  have hu1 : u1 ∈ LB := by rw [hdec]; simp
  have hu2 : u2 ∈ LB := by rw [hdec]; simp
  obtain ⟨TB, -, hTB, -, hposB⟩ := walkU_pos wB
  have hTT : T = TB := param_unique hd (hT.symm.trans hTB)
  obtain ⟨a1, b1, ha1, hb1, ha1', hlt1, hle1⟩ := hposB u1 hu1
  obtain ⟨a2, b2, ha2, hb2, ha2', hlt2, hle2⟩ := hposB u2 hu2
  -- parameter of W
  have hWs : b1 = a2 := by
    apply param_unique hd
    rw [← hb1, ← ha2, hadj]
  set s := b1 with hs
  have hs0 : 0 < s := by linarith
  have hsT : s < T := by rw [hTT]; linarith
  have hWpar : toV2 (W - X) = (s * d.1, s * d.2) := hb1
  -- W is strictly inside an element of LA
  obtain ⟨g, hg, g0, g1, hg0, hg1, hg01, hgs⟩ := walkU_cover' wA hd hT s hs0 hsT.le
  have hne1 : s ≠ g1 := by
    intro e
    apply hnA
    refine ⟨g, hg, ?_⟩
    apply pt_eq_of_toV2 (H := X)
    rw [hg1, hWpar, e]
  have hlt : s < g1 := lt_of_le_of_ne hgs hne1
  have hσ0 : 0 < (s - g0) / (g1 - g0) := div_pos (by linarith) (by linarith)
  have hσ1 : (s - g0) / (g1 - g0) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hWg : W = g.2.1 + ((s - g0) / (g1 - g0)) • (g.2.2 - g.2.1) := pt_on_step hg01 hgs hg0 hg1 hWpar
  -- the transition gives an edge from W
  have hSA : StepU D.toRegionDissection (!bA) d u1 := walkU_mem_step wB u1 hu1
  have hSB : StepU D.toRegionDissection (!bA) d u2 := walkU_mem_step wB u2 hu2
  have hSg : StepU D.toRegionDissection (!(!bA)) d g := by simpa using walkU_mem_step wA g hg
  obtain ⟨H', hH'⟩ := gc_trans_walk D idx h hSA hSB hadj hSg hσ0 hσ1 hWg hord
  have hWmax : nsq (toV2 u1.2.2) ≤ nsq (toV2 V) := hext _ _ hH'
  have hdpos : 0 < d.1 ^ 2 + d.2 ^ 2 := nsq_pos hd
  have hXV : nsq (toV2 X) ≤ nsq (toV2 V) := by
    obtain ⟨H1, hE1⟩ := (⟨V, hEXV⟩ : ∃ H, GcEdge D X H)
    exact hext X V hEXV
  rcases lt_trichotomy s sV with hlts | heq | hgt
  · -- W before V: arrival
    obtain ⟨Z, hZ⟩ := gc_in_of_out D Pg hreg idx h hH'
    have hZW : GcEdge D Z W := hZ
    rcases hArr d X Y W Z bA LA LB hd hnb wA wB hLA hLB nc1 nc2 ⟨u1, hu1, rfl⟩ ⟨g, hg, _, hσ0, hσ1, hWg⟩ hZW with hZX | ⟨z, T', hz, hT', hTz⟩
    · subst hZX
      have := gc_out_unique D Pg hreg idx h hZW hEXV
      have e1 : toV2 (W - Z) = (s * d.1, s * d.2) := hWpar
      have e2 : toV2 (V - Z) = (sV * d.1, sV * d.2) := hV
      rw [this] at e1
      have := param_unique hd (e1.symm.trans e2)
      linarith
    · have hTT' : T' = T := param_unique hd (hT'.symm.trans hT)
      subst hTT'
      have hZmax : nsq (toV2 Z) ≤ nsq (toV2 V) := hext Z W hZW
      have := nsq_convex (X := toV2 X) (V := toV2 V) (P := toV2 Z) (d := d) hdpos (toV2_pt hV) (toV2_pt hz) hsV (by linarith) hXV
      unfold nsq at hZmax
      linarith
  · -- W = V is impossible: V is an end of an element of LA
    apply hnA
    obtain ⟨g', hg', hgV⟩ := hVA
    refine ⟨g', hg', ?_⟩
    rw [hgV]
    apply pt_eq_of_toV2 (H := X)
    rw [hV, hWpar, heq]
  · -- W after V: convexity
    have := nsq_convex (X := toV2 X) (V := toV2 V) (P := toV2 W) (d := d) hdpos (toV2_pt hV) (toV2_pt hWpar) hsV hgt hXV
    unfold nsq at hWmax
    linarith

theorem chain_all {α : Type*} (S : α → Prop) : ∀ (Q : List α), (∀ Q1 u1 u2 Q2, Q = Q1 ++ u1 :: u2 :: Q2 → (S u1 ↔ S u2)) →
    (∀ q ∈ Q.head?, ¬ S q) → ∀ u ∈ Q, ¬ S u := by
  intro Q
  induction Q with
  | nil => intro _ _ u hu; exact absurd hu (by simp)
  | cons q Q ih =>
    intro hpair hhd u hu
    have hq : ¬ S q := hhd q (by simp)
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact hq
    · apply ih (fun Q1 u1 u2 Q2 hQ => hpair (q :: Q1) u1 u2 Q2 (by rw [hQ]; rfl)) _ u hu'
      intro q' hq'
      cases Q with
      | nil => simp at hq'
      | cons q2 Q2 =>
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq'
        rw [← hq']
        exact fun hS => hq ((hpair [] q q2 Q2 rfl).mpr hS)

theorem stepU_len_mem (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {b : Bool} {d : V2} {e : Fin N × Plane × Plane} (h : StepU D.toRegionDissection b d e) :
    dist e.2.1 e.2.2 = slen D 0 ∨ dist e.2.1 e.2.2 = slen D 1 ∨ dist e.2.1 e.2.2 = slen D 2 := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at h
    rw [dist_comm]; exact side_len_mem D idx hidx h
  · simp only [StepU, if_true] at h
    exact side_len_mem D idx hidx h

/-- **Lemma 4.6 (Laczkovich, DCG 48 (2012)), polygon version, conditional on `Arrival D`**: if `a, b` are commensurable and `c` is not a rational multiple of `a`, then `Γ_c` has no edge. -/
theorem gc_empty_of_arrival (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (Pg : ConvPoly M) (hreg : D.region = Pg.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hArr : Arrival D)
    (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2)) : ∀ X H, ¬ GcEdge D X H := by
  classical
  intro X0 H0 hE0
  -- the finite set `G` of tails and an extreme point `V`
  set G : Finset Plane := (vtxSet D.toRegionDissection).filter (fun v => ∃ H, GcEdge D v H) with hGdef
  have hX0 : X0 ∈ G := by
    simp only [hGdef, Finset.mem_filter]
    exact ⟨mem_vtxSet.mpr (ga_edge_endpoints D.toRegionDissection (slen D 2) hE0).1, H0, hE0⟩
  obtain ⟨V, hVG, hVmax⟩ := Finset.exists_max_image G (fun v => nsq (toV2 v)) ⟨X0, hX0⟩
  have hext : ExtV D V := by
    intro v H hE
    apply hVmax
    simp only [hGdef, Finset.mem_filter]
    exact ⟨mem_vtxSet.mpr (ga_edge_endpoints D.toRegionDissection (slen D 2) hE).1, H, hE⟩
  have hVout : ∃ H, GcEdge D V H := by simp only [hGdef, Finset.mem_filter] at hVG; exact hVG.2
  obtain ⟨H1, hE1⟩ := hVout
  obtain ⟨X, hXV⟩ := gc_in_of_out D Pg hreg idx h hE1
  obtain ⟨d, Y, bA, LA, LB, hd, hnb, wA, wB, hLA, hLB, nc1, nc2, hRun, hhd⟩ := gcEdge_unpack D hXV
  obtain ⟨L', e, L'', hdec, hL'ne, hall, hnot, hVe⟩ := hRun
  have hdpos : 0 < nsq d := nsq_pos hd
  -- the prefix up to `V`
  obtain ⟨wpre, wsuf⟩ := walkU_split wA hdec
  rw [← hVe] at wpre
  obtain ⟨sV, hsV0, hV, hsVp, -⟩ := walkU_pos wpre
  have hsVpos : 0 < sV := hsVp hL'ne
  obtain ⟨T, hT0, hT, hTp, hposA⟩ := walkU_pos wA
  have heA : e ∈ LA := by rw [hdec]; simp
  obtain ⟨e0, e1, he0, he1, he00, he01, he1T⟩ := hposA e heA
  have hse0 : e0 = sV := by
    have hV' := hV
    rw [hVe] at hV'
    exact param_unique hd (he0.symm.trans hV')
  have hsVT : sV < T := by linarith
  have hVA : ∃ g ∈ LA, g.2.2 = V := by
    obtain ⟨g, hg, hgV⟩ := walkU_last wpre hL'ne
    exact ⟨g, by rw [hdec]; exact List.mem_append_left _ hg, by rw [hgV]⟩
  have hXVmax : nsq (toV2 X) ≤ nsq (toV2 V) := hext X V hXV
  -- first common end
  set AE : Finset Plane := (LA.map (fun x => x.2.2)).toFinset with hAE
  set C : Finset Plane := AE.filter (fun U => ∃ f ∈ LB, f.2.2 = U) with hCdef
  have hYC : Y ∈ C := by
    simp only [hCdef, hAE, Finset.mem_filter, List.mem_toFinset, List.mem_map]
    obtain ⟨g, hg, hgY⟩ := walkU_last wA hLA
    obtain ⟨f, hf, hfY⟩ := walkU_last wB hLB
    exact ⟨⟨g, hg, hgY⟩, f, hf, hfY⟩
  obtain ⟨Ul, hUlC, hUlmin⟩ := Finset.exists_min_image C (fun U => dt d (toV2 (U - X))) ⟨Y, hYC⟩
  have hUlC' := hUlC
  simp only [hCdef, hAE, Finset.mem_filter, List.mem_toFinset, List.mem_map] at hUlC'
  obtain ⟨⟨eS, heS, heSU⟩, fS, hfS, hfSU⟩ := hUlC'
  obtain ⟨PB, SB, hLBdec⟩ := List.append_of_mem hfS
  obtain ⟨PA, SA, hLAdec⟩ := List.append_of_mem heS
  obtain ⟨iS, AS, BS⟩ := fS
  obtain ⟨iE, AE', BE'⟩ := eS
  simp only at hfSU heSU
  subst hfSU
  -- prefix walks to `Ul`
  have wBpre : WalkU D.toRegionDissection (!bA) d X BS (PB ++ [(iS, AS, BS)]) := by
    obtain ⟨w1, w2⟩ := walkU_split wB hLBdec
    rw [walkU_append]
    cases w2 with
    | cons hS W' => exact ⟨AS, w1, WalkU.cons hS (WalkU.nil _)⟩
  have wApre : WalkU D.toRegionDissection bA d X BS (PA ++ [(iE, AE', BS)]) := by
    rw [← heSU] at *
    obtain ⟨w1, w2⟩ := walkU_split wA hLAdec
    rw [walkU_append]
    cases w2 with
    | cons hS W' => exact ⟨AE', w1, WalkU.cons hS (WalkU.nil _)⟩
  set fB : Fin N × Plane × Plane := (iS, AS, BS) with hfB
  set eA : Fin N × Plane × Plane := (iE, AE', BS) with heA'
  -- positions along the prefix
  obtain ⟨TU, -, hTU, -, hposU⟩ := walkU_pos wBpre
  have dt_param : ∀ {P : Plane} {t : ℝ}, toV2 (P - X) = (t * d.1, t * d.2) → dt d (toV2 (P - X)) = t * nsq d := by
    intro P t hP
    rw [hP]; unfold dt nsq; simp only; ring
  -- all elements of the prefix of `LB` have the status of the first one: not `c`
  have hpair : ∀ Q1 u1 u2 Q2, PB ++ [fB] = Q1 ++ u1 :: u2 :: Q2 → (dist u1.2.1 u1.2.2 = slen D 2 ↔ dist u2.2.1 u2.2.2 = slen D 2) := by
    intro Q1 u1 u2 Q2 hQ
    by_contra hne
    have hord : (dist u1.2.1 u1.2.2 = slen D 2 ∧ dist u2.2.1 u2.2.2 ≠ slen D 2) ∨ (dist u1.2.1 u1.2.2 ≠ slen D 2 ∧ dist u2.2.1 u2.2.2 = slen D 2) := by
      by_cases h1 : dist u1.2.1 u1.2.2 = slen D 2
      · left; exact ⟨h1, fun h2 => hne ⟨fun _ => h2, fun _ => h1⟩⟩
      · right; exact ⟨h1, by_contra fun h2 => hne ⟨fun h => absurd h h1, fun h => absurd h h2⟩⟩
    have hLB' : LB = Q1 ++ u1 :: u2 :: (Q2 ++ SB) := by
      rw [hLBdec]
      have : PB ++ (iS, AS, BS) :: SB = (PB ++ [fB]) ++ SB := by simp [hfB]
      rw [this, hQ]; simp
    have hu2 : u2 ∈ PB ++ [fB] := by rw [hQ]; simp
    have hadj : u1.2.2 = u2.2.1 := walkU_adj (b := !bA) (hLB' ▸ wB)
    have hadj' : u1.2.2 = u2.2.1 := hadj
    obtain ⟨t0, t1, h0, h1, h00, h01, h1T⟩ := hposU u2 hu2
    refine no_transition D Pg hreg idx h hArr hd hnb wA wB hLA hLB nc1 nc2 hext hXV hsVpos hV hT hsVT hVA hLB' ?_ hord
    rintro ⟨g, hg, hgW⟩
    have hmemC : u1.2.2 ∈ C := by
      simp only [hCdef, hAE, Finset.mem_filter, List.mem_toFinset, List.mem_map]
      refine ⟨⟨g, hg, hgW⟩, u1, ?_, rfl⟩
      rw [hLB']; simp
    have hle := hUlmin _ hmemC
    have hW : toV2 (u1.2.2 - X) = (t0 * d.1, t0 * d.2) := by rw [hadj']; exact h0
    simp only at hle
    rw [dt_param hW, dt_param hTU] at hle
    nlinarith
  have hnonc : ∀ u ∈ PB ++ [fB], ¬ (dist u.2.1 u.2.2 = slen D 2) := by
    apply chain_all _ _ hpair
    intro q hq
    apply hhd q
    cases PB with
    | nil =>
      simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      rw [hLBdec]; simp [← hq]
    | cons p PB0 =>
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      rw [hLBdec]; simp [← hq]
  -- count of `c` on the two sides
  have hlenA : ∀ x ∈ (PA ++ [eA]).map (fun x => dist x.2.1 x.2.2), x = slen D 0 ∨ x = slen D 1 ∨ x = slen D 2 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact stepU_len_mem D idx h.hidx (walkU_mem_step wApre u hu)
  have hlenB : ∀ x ∈ (PB ++ [fB]).map (fun x => dist x.2.1 x.2.2), x = slen D 0 ∨ x = slen D 1 ∨ x = slen D 2 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    exact stepU_len_mem D idx h.hidx (walkU_mem_step wBpre u hu)
  have hsum : ((PA ++ [eA]).map (fun x => dist x.2.1 x.2.2)).sum = ((PB ++ [fB]).map (fun x => dist x.2.1 x.2.2)).sum := by
    rw [walkU_dist_sum wApre, walkU_dist_sum wBpre]
  have hcnt := count_c_eq (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) hab hac _ _ hlenA hlenB hsum
  have hcB : ((PB ++ [fB]).map (fun x => dist x.2.1 x.2.2)).count (slen D 2) = 0 := by
    apply List.count_eq_zero.mpr
    intro hm
    obtain ⟨u, hu, hue⟩ := List.mem_map.mp hm
    exact hnonc u hu hue
  have hcA : 1 ≤ ((PA ++ [eA]).map (fun x => dist x.2.1 x.2.2)).count (slen D 2) := by
    apply List.count_pos_iff.mpr
    obtain ⟨x, L'0, hL'x⟩ := List.exists_cons_of_ne_nil hL'ne
    have hxc : dist x.2.1 x.2.2 = slen D 2 := hall x (by rw [hL'x]; simp)
    have hLAx : LA = x :: (L'0 ++ e :: L'') := by rw [hdec, hL'x]; rfl
    have hxmem : x ∈ PA ++ [eA] := by
      cases PA with
      | nil =>
        rw [hLAdec] at hLAx
        simp only [List.nil_append, List.cons.injEq] at hLAx
        simp [← hLAx.1, heA', heSU]
      | cons p PA0 =>
        rw [hLAdec] at hLAx
        simp only [List.cons_append, List.cons.injEq] at hLAx
        simp [← hLAx.1]
    exact List.mem_map.mpr ⟨x, hxmem, hxc⟩
  omega

end Erdos634.Draft.LaczFormal.RG
