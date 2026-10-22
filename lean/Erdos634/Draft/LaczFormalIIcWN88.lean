-- Draft/LaczFormalIIcWN88.lean -- Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5(B)), R2 (tile level): the START of Gamma_except at a non-straight vertex of Gamma_kite, WITH DIRECTION.
-- `gexc_start_dir` is `gexc_start_of_kite` (RG12GExcStart) with the ray `h` made explicit: the edge `Y -> W` leaves `Y` into the `alpha+beta` wedge between the two kite axes, along `rot beta (X - Y)`
-- (case A: `Z - Y = rot (alpha+beta) (X - Y)`, i.e. a right turn of a counterclockwise chain) or along `rot alpha (Z - Y)` (case B: `X - Y = rot (alpha+beta) (Z - Y)`).
-- The proof is that of `gexc_start_of_kite` (copied, since that statement only gives `exists W`); the four label cases of `comb_B` now also record the rotations along the runs of the fan (`run_rotation`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExcStart
import Erdos634.Draft.LaczFormalIIcSpoke3
import Erdos634.Draft.LaczFormalIIcWN87

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem gexc_wit_ray_T {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {d : V2} {Y Z' H1 : Plane} {L1 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d Y Z' L1) (hr1 : GRunEnd D idx L1 H1) : ∃ T : ℝ, 0 < T ∧ toV2 (H1 - Y) = (T * d.1, T * d.2) := by
  obtain ⟨L', L'', hL, -, -, -, e0, hlast, he0⟩ := hr1
  have hmem : e0 ∈ L1 := by rw [hL]; exact List.mem_append_left _ (List.mem_of_getLast? hlast)
  obtain ⟨T, hT, hTe⟩ := walkT_head_ray W1 e0 hmem
  exact ⟨T, hT, by rw [← he0]; exact hTe⟩

theorem gexc_wit_ray_R {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} {d : V2} {Y Z' H2 : Plane} {L2 : List (Fin N × Plane × Plane)}
    (W2 : WalkR D.toRegionDissection d Y Z' L2) (hr2 : GRunEnd D idx L2 H2) : ∃ T : ℝ, 0 < T ∧ toV2 (H2 - Y) = (T * d.1, T * d.2) := by
  obtain ⟨L', L'', hL, -, -, -, e0, hlast, he0⟩ := hr2
  have hmem : e0 ∈ L2 := by rw [hL]; exact List.mem_append_left _ (List.mem_of_getLast? hlast)
  obtain ⟨T, hT, hTe⟩ := walkR_head_ray W2 e0 hmem
  exact ⟨T, hT, by rw [← he0]; exact hTe⟩

theorem par_smul_pos {T : ℝ} {u v : V2} (hT : 0 < T) (h : Par u v) : Par ((T * u.1, T * u.2) : V2) v := by
  refine ⟨?_, ?_⟩
  · have := h.1; unfold crs at this ⊢; simp only; linear_combination T * this
  · have := h.2; unfold dt at this ⊢; simp only; nlinarith

set_option maxHeartbeats 6400000 in
/-- **Start of Gamma_except at a non-straight Gamma_kite vertex, with direction.** -/
theorem gexc_start_dir [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3)
    (G : AngGen (fun l => D.model.angleAt l)) {X Y Z : Plane} (hXY : GKite D idx X Y) (hYZ : GKite D idx Y Z) (hB : ¬ StraightAt D Y) :
    ∃ W, GExc D idx Y W ∧
      ((toV2 (Z - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (X - Y)) ∧ Par (toV2 (W - Y)) (Graph.rot (D.model.angleAt 1) (toV2 (X - Y)))) ∨
       (toV2 (X - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (Z - Y)) ∧ Par (toV2 (W - Y)) (Graph.rot (D.model.angleAt 0) (toV2 (Z - Y))))) := by
  classical
  have hdist := gkite_dist_eq D idx hC hXY hYZ
  obtain ⟨⟨hVint, c0, c1, c2⟩, -⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXY
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, hperS⟩ := fan222_tile D idx hC.hidxA hVint c0 c1 c2 G
  have hpar : ∀ j, Par (F.p (s (j + 1))) (F.q (s j)) := fun j => hF.hpar j
  have hmodS := per_mod s hperS
  have hperL : ∀ n, ℓ (n + 6) = ℓ n := by
    intro n
    obtain ⟨k, hk, -⟩ := hlab n
    have hk' : (D.tile (s (n + 6)).1).pts k = Y := by rw [hperS n]; exact hk
    have h1' := label_eq hlab (j := n + 6) rfl hk'
    have h2' := label_eq hlab (j := n) rfl hk
    rw [← h1', ← h2', hperS n]
  -- corner data of every sector
  have hsec : ∀ n, ∃ kk fl, (D.tile (s n).1).pts kk = Y ∧ F.p (s n) = toV2 ((D.tile (s n).1).pts (armP kk fl) - Y) ∧
      F.q (s n) = toV2 ((D.tile (s n).1).pts (armQ kk fl) - Y) ∧ idx (s n).1 kk = ℓ n := by
    intro n
    obtain ⟨k, hk, -⟩ := hlab n
    obtain ⟨kk, fl, hkk, hp, hq⟩ := spec_corner_data (F.hspec (s n)) ⟨k, hk⟩
    exact ⟨kk, fl, hkk, hp, hq, label_eq hlab rfl hkk⟩
  have hsum : ∀ (i : Fin N) (kk : Fin 3) (fl : Bool), (idx i kk).val + (idx i (armP kk fl)).val + (idx i (armQ kk fl)).val = 3 := fun i kk fl =>
    fin3_sum3 (fun h => armP_ne kk fl ((idx i).injective h).symm) (fun h => armQ_ne kk fl ((idx i).injective h).symm)
      (fun h => armPQ_ne kk fl ((idx i).injective h))
  have hstart : ∀ n (d : V2), Par (F.p (s n)) d → ∃ U, TriStep (D.tile (s n).1) d Y U := by
    intro n d hd
    obtain ⟨kk, fl, hkk, hp, hq, -⟩ := hsec n
    exact ⟨_, triStep_of_start kk fl hkk hp hq (crs_pos_of_corner (F.hok (s n)) (F.hspec (s n)) ⟨kk, hkk⟩) hd⟩
  have hend : ∀ n (d : V2), Par (F.q (s n)) d → ∃ U, TriStep (D.tile (s n).1) (neg2 d) U Y := by
    intro n d hd
    obtain ⟨kk, fl, hkk, hp, hq, -⟩ := hsec n
    exact ⟨_, triStep_of_end kk fl hkk hp hq (crs_pos_of_corner (F.hok (s n)) (F.hspec (s n)) ⟨kk, hkk⟩) hd⟩
  -- far labels: PF n = the p-side of the sector s n has far label gamma; QF n = the q-side has
  obtain ⟨PF, hPF⟩ : ∃ PF : ℕ → Prop, ∀ n, PF n ↔ ∃ kk fl, (D.tile (s n).1).pts kk = Y ∧ F.p (s n) = toV2 ((D.tile (s n).1).pts (armP kk fl) - Y) ∧
      F.q (s n) = toV2 ((D.tile (s n).1).pts (armQ kk fl) - Y) ∧ idx (s n).1 (armP kk fl) = 2 := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨QF, hQF⟩ : ∃ QF : ℕ → Prop, ∀ n, QF n ↔ ∃ kk fl, (D.tile (s n).1).pts kk = Y ∧ F.p (s n) = toV2 ((D.tile (s n).1).pts (armP kk fl) - Y) ∧
      F.q (s n) = toV2 ((D.tile (s n).1).pts (armQ kk fl) - Y) ∧ idx (s n).1 (armQ kk fl) = 2 := ⟨_, fun _ => Iff.rfl⟩
  have hPF6 : ∀ n, PF (n + 6) ↔ PF n := by intro n; rw [hPF, hPF, hperS n]
  have hPF_end : ∀ n (i : Fin N) (d : V2) (X' : Plane), TriStep (D.tile i) d X' Y → (s n).1 = i → ∀ kx, (D.tile i).pts kx = X' → ∀ a : Fin 3, idx i kx = a →
      (ℓ n).val + a.val = 1 → PF n := by
    intro n i d X' hS hi kx hkx a ha hsm
    subst hi
    obtain ⟨kk, fl, hkk, hp, hq, hl⟩ := hsec n
    obtain ⟨k2, hk2, hk2e⟩ := arm_end_eq hS kk fl hkk hp hq (F.hok (s n))
    have hk2x : k2 = kx := (D.tile (s n).1).indep.injective (hk2.trans hkx.symm)
    have hq2 : idx (s n).1 (armQ kk fl) = a := by rw [← hk2e, hk2x]; exact ha
    have := hsum (s n).1 kk fl
    rw [hl, hq2] at this
    refine (hPF n).2 ⟨kk, fl, hkk, hp, hq, Fin.ext (by simp; omega)⟩
  have hQF_start : ∀ n (i : Fin N) (d : V2) (X' : Plane), TriStep (D.tile i) d Y X' → (s n).1 = i → ∀ kx, (D.tile i).pts kx = X' → ∀ a : Fin 3, idx i kx = a →
      (ℓ n).val + a.val = 1 → QF n := by
    intro n i d X' hS hi kx hkx a ha hsm
    subst hi
    obtain ⟨kk, fl, hkk, hp, hq, hl⟩ := hsec n
    obtain ⟨k2, hk2, hk2e⟩ := arm_start_eq hS kk fl hkk hp hq (F.hok (s n))
    have hk2x : k2 = kx := (D.tile (s n).1).indep.injective (hk2.trans hkx.symm)
    have hp2 : idx (s n).1 (armP kk fl) = a := by rw [← hk2e, hk2x]; exact ha
    have := hsum (s n).1 kk fl
    rw [hl, hp2] at this
    refine (hQF n).2 ⟨kk, fl, hkk, hp, hq, Fin.ext (by simp; omega)⟩
  -- the head kite XY (beta beta)
  obtain ⟨iB, jB, dB, kkB, fB, kkB', fB', -, hSiB, hSjB, hkB, hfB, hikB, hifB, hkB', hfB', hjkB, hjfB⟩ := hXY
  obtain ⟨yB1, hyB1i, hyB1q⟩ := sec_end F hSiB
  obtain ⟨yB2, hyB2i, hyB2p⟩ := sec_start F hSjB
  obtain ⟨b0, hb0, hsb0⟩ := hsurj yB1
  have hyB2 : yB2 = s (b0 + 1) := next_sector F s hpar (j := b0) (by rw [hsb0]; exact hyB1q) hyB2p
  have hiB : (s b0).1 = iB := by rw [hsb0]; exact hyB1i
  have hjB : (s (b0 + 1)).1 = jB := by rw [← hyB2]; exact hyB2i
  have hlb : ℓ b0 = 1 := by rw [← hifB]; exact (label_eq hlab (j := b0) hiB hfB).symm
  have hlb1 : ℓ (b0 + 1) = 1 := by rw [← hjkB]; exact (label_eq hlab (j := b0 + 1) hjB hkB').symm
  have hPFb : PF b0 := hPF_end b0 iB dB X hSiB hiB kkB hkB 0 hikB (by rw [hlb]; rfl)
  have hQFb : QF (b0 + 1) := hQF_start (b0 + 1) jB (neg2 dB) X hSjB hjB fB' hfB' 0 hjfB (by rw [hlb1]; rfl)
  -- the tail kite YZ (alpha alpha)
  obtain ⟨iA, jA, dA, kkA, fA, kkA', fA', -, hSiA, hSjA, hkA, hfA, hikA, hifA, hkA', hfA', hjkA, hjfA⟩ := hYZ
  obtain ⟨yA2, hyA2i, hyA2p⟩ := sec_start F hSiA
  obtain ⟨yA1, hyA1i, hyA1q⟩ := sec_end F hSjA
  obtain ⟨c0', hc0', hsc0⟩ := hsurj yA1
  have hyA2 : yA2 = s (c0' + 1) := next_sector F s hpar (j := c0') (r := dA) (by rw [hsc0]; rw [neg2_neg2'] at hyA1q; exact hyA1q) hyA2p
  have hjA : (s c0').1 = jA := by rw [hsc0]; exact hyA1i
  have hiA : (s (c0' + 1)).1 = iA := by rw [← hyA2]; exact hyA2i
  have hlc : ℓ c0' = 0 := by rw [← hjfA]; exact (label_eq hlab (j := c0') hjA hfA').symm
  have hlc1 : ℓ (c0' + 1) = 0 := by rw [← hikA]; exact (label_eq hlab (j := c0' + 1) hiA hkA).symm
  have hPFc : PF c0' := hPF_end c0' jA (neg2 dA) Z hSjA hjA kkA' hkA' 1 hjkA (by rw [hlc]; rfl)
  have hQFc : QF (c0' + 1) := hQF_start (c0' + 1) iA dA Z hSiA hiA fA hfA 1 hifA (by rw [hlc1]; rfl)
  -- no straight line: no three consecutive pairwise distinct labels
  have hnt : ∀ j, ¬ (ℓ j ≠ ℓ (j + 1) ∧ ℓ j ≠ ℓ (j + 2) ∧ ℓ (j + 1) ≠ ℓ (j + 2)) := by
    rintro j ⟨h01, h02, h12⟩
    have hopp := straight_of_triple G hF j h01 h02 h12
    apply hB
    have hq5 : Par (F.q (s (j + 5))) (F.p (s j)) := by
      have := hpar (j + 5)
      rw [show j + 5 + 1 = j + 6 by omega, hperS j] at this
      exact this.symm
    obtain ⟨A, hA⟩ := hend (j + 5) (F.p (s j)) hq5
    obtain ⟨B', hB'⟩ := hstart j (neg2 (neg2 (F.p (s j)))) (by rw [neg2_neg2']; exact par_refl (hF.hu j))
    obtain ⟨W, hW⟩ := hstart (j + 3) (neg2 (F.p (s j))) hopp
    exact ⟨neg2 (F.p (s j)), A, B', W, _, _, _, hA, hB', hW⟩
  have hc0 : ((Finset.range 6).filter (fun i => ℓ i = 0)).card = 2 := by
    have := hF.hcnt 0 0; simpa only [zero_add] using this
  have hc1 : ((Finset.range 6).filter (fun i => ℓ i = 1)).card = 2 := by
    have := hF.hcnt 0 1; simpa only [zero_add] using this
  -- the final construction at a ray `h` between the end of `s m` and the start of `s (m+1)`
  have final : ∀ m, QF m → PF (m + 1) → ∃ W, GExc D idx Y W ∧ ∃ T : ℝ, 0 < T ∧ toV2 (W - Y) = (T * (F.p (s (m + 1))).1, T * (F.p (s (m + 1))).2) := by
    intro m hQm hPm
    obtain ⟨kq, flq, hkq, hpq, hqq, hlq⟩ := (hQF m).1 hQm
    obtain ⟨kp, flp, hkp, hpp, hqp, hlp⟩ := (hPF (m + 1)).1 hPm
    set d := F.p (s (m + 1)) with hd_def
    have hd0 : d ≠ 0 := hF.hu (m + 1)
    have hnop : ∀ n, ¬ Par (F.p (s n)) (neg2 d) := by
      intro n h
      by_cases hn : n % 6 = (m + 1) % 6
      · have hs : s n = s (m + 1) := by rw [hmodS n, hmodS (m + 1), hn]
        rw [hs] at h
        exact not_par_neg2 hd0 h
      · have hm1 : 1 ≤ (n + 6 - (m + 1) % 6) % 6 := by omega
        have hm5 : (n + 6 - (m + 1) % 6) % 6 ≤ 5 := by omega
        have hss : s (m + 1 + (n + 6 - (m + 1) % 6) % 6) = s n := by
          rw [hmodS (m + 1 + (n + 6 - (m + 1) % 6) % 6), hmodS n]; congr 1; omega
        have hstr : Par (F.p (s (m + 1 + (n + 6 - (m + 1) % 6) % 6))) (-(F.p (s (m + 1))).1, -(F.p (s (m + 1))).2) := by rw [hss]; exact h
        obtain ⟨-, a1, a2, a3⟩ := straight_run_labels G hF (m + 1) _ hm1 hm5 hstr
        exact hnt (m + 1) ⟨a1, a2, a3⟩
    have hnb : NoBack D.toRegionDissection d Y := by
      apply ExtFan.noBack_of_none F
      intro x
      obtain ⟨j, -, hjs⟩ := hsurj x
      subst hjs
      exact ⟨hnop j, fun h => hnop (j + 1) ((hpar j).trans h)⟩
    have hcrs : ∀ n, 0 < crs (F.p (s n)) (F.q (s n)) := fun n => by
      obtain ⟨kk, fl, hkk, -⟩ := hsec n
      exact crs_pos_of_corner (F.hok (s n)) (F.hspec (s n)) ⟨kk, hkk⟩
    have hl0 : TriStep (D.tile (s (m + 1)).1) d Y ((D.tile (s (m + 1)).1).pts (armP kp flp)) :=
      triStep_of_start kp flp hkp hpp hqp (hcrs (m + 1)) (par_refl hd0)
    have hr0 : TriStep (D.tile (s m).1) (neg2 d) ((D.tile (s m).1).pts (armQ kq flq)) Y :=
      triStep_of_end kq flq hkq hpq hqq (hcrs m) (hpar m).symm
    have hvert : ∃ j k, (D.tile j).pts k = Y := ⟨(s (m + 1)).1, kp, hkp⟩
    obtain ⟨Z', L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd0 hvert ⟨_, _, hl0⟩ ⟨_, _, hr0⟩
    obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) d e1.2.1 e1.2.2 ∧ e1.2.1 = Y := by
      cases W1 with
      | nil => exact absurd rfl hL1
      | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
    obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 d) e2.2.2 e2.2.1 ∧ e2.2.1 = Y := by
      cases W2 with
      | nil => exact absurd rfl hL2
      | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
    rw [he1X] at hS1
    rw [he2X] at hS2
    obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl0
    obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr0
    have hg1 : GammaHead D idx e1 := ⟨armP kp flp, by rw [hU1, hi1], by rw [hi1]; exact hlp⟩
    have hg2 : GammaHead D idx e2 := ⟨armQ kq flq, by rw [hU2, hi2], by rw [hi2]; exact hlq⟩
    obtain ⟨H1, hr1⟩ := grunEnd_exists D idx hL1 (by rw [hL1e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hg1)
    obtain ⟨H2, hr2⟩ := grunEnd_exists D idx hL2 (by rw [hL2e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hg2)
    rcases le_total (dist Y H1) (dist Y H2) with hle | hle
    · exact ⟨H1, ⟨d, Z', L1, L2, H1, H2, hd0, hnb, W1, W2, hL1, hL2, hno1, hno2, hr1, hr2, Or.inl ⟨rfl, hle⟩⟩, gexc_wit_ray_T W1 hr1⟩
    · exact ⟨H2, ⟨d, Z', L1, L2, H1, H2, hd0, hnb, W1, W2, hL1, hL2, hno1, hno2, hr1, hr2, Or.inr ⟨rfl, hle⟩⟩, gexc_wit_ray_R W2 hr2⟩
  -- rotations along runs of the fan
  have rv : ∀ j m, Par (F.p (s (j + m))) (Graph.rot (∑ i ∈ Finset.range m, wd (F.p (s (j + i))) (F.q (s (j + i)))) (F.p (s j))) := by
    intro j m
    have := run_rotation (fun i => F.p (s (j + i))) (fun i => F.q (s (j + i))) (fun i => hF.hu (j + i)) (fun i => by
      have := hF.hpar (j + i); simpa [add_assoc] using this) m
    simpa using this
  have hwdl : ∀ i, wd (F.p (s i)) (F.q (s i)) = D.model.angleAt (ℓ i) := fun i => hF.hwd i
  have hXu : Par (F.p (s (b0 + 1))) (toV2 (X - Y)) := by
    have e1 : Par (F.p yB2) (neg2 dB) := hyB2p
    rw [hyB2] at e1
    have hYX : Par (toV2 (Y - X)) dB := by obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSiB; exact hp
    exact e1.trans (par_neg_arm hYX).symm
  have hZu : Par (F.p (s (c0' + 1))) (toV2 (Z - Y)) := by
    have e1 : Par (F.p yA2) dA := hyA2p
    rw [hyA2] at e1
    have hZY : Par (toV2 (Z - Y)) dA := by obtain ⟨-, -, -, -, -, -, -, -, hp, -⟩ := hSiA; exact hp
    exact e1.trans hZY.symm
  have hnorm : nsq (toV2 (Z - Y)) = nsq (toV2 (X - Y)) := by
    rw [nsq_toV2, nsq_toV2, dist_comm Z Y]; exact (congrArg (· ^ 2) hdist).symm
  have caseA : (b0 + 2 = c0' ∨ b0 + 2 = c0' + 6) → ∃ W, GExc D idx Y W ∧
      ((toV2 (Z - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (X - Y)) ∧ Par (toV2 (W - Y)) (Graph.rot (D.model.angleAt 1) (toV2 (X - Y)))) ∨
       (toV2 (X - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (Z - Y)) ∧ Par (toV2 (W - Y)) (Graph.rot (D.model.angleAt 0) (toV2 (Z - Y))))) := by
    intro hc
    have hP : PF (b0 + 1 + 1) := by
      rcases hc with hc | hc
      · rw [show b0 + 1 + 1 = c0' by omega]; exact hPFc
      · rw [show b0 + 1 + 1 = c0' + 6 by omega]; exact (hPF6 c0').2 hPFc
    obtain ⟨W, hW, T, hT, hTe⟩ := final (b0 + 1) hQFb hP
    have hlc' : ℓ (b0 + 1 + 1) = 0 := by
      rcases hc with hc | hc
      · rw [show b0 + 1 + 1 = c0' by omega]; exact hlc
      · rw [show b0 + 1 + 1 = c0' + 6 by omega, hperL]; exact hlc
    have hs : s (b0 + 1 + 2) = s (c0' + 1) := by
      rcases hc with hc | hc
      · rw [show b0 + 1 + 2 = c0' + 1 by omega]
      · rw [show b0 + 1 + 2 = c0' + 1 + 6 by omega, hperS]
    have h2 := rv (b0 + 1) 2
    have h1r := rv (b0 + 1) 1
    rw [hs] at h2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h2
    rw [Finset.sum_range_succ, Finset.sum_range_zero] at h1r
    simp only [zero_add, add_zero, hwdl, hlb1, hlc'] at h2 h1r
    refine ⟨W, hW, Or.inl ⟨?_, ?_⟩⟩
    · have h2' : Par (toV2 (Z - Y)) (Graph.rot (D.model.angleAt 1 + D.model.angleAt 0) (toV2 (X - Y))) :=
        hZu.symm.trans (h2.trans (par_rot _ hXu))
      have hrr := eq_of_par_nsq h2' (by rw [nsq_rot]; exact hnorm)
      rw [hrr, add_comm]
    · rw [hTe]
      exact par_smul_pos hT (h1r.trans (par_rot _ hXu))
  have caseB : (c0' + 2 = b0 ∨ c0' + 2 = b0 + 6) → ∃ W, GExc D idx Y W ∧
      ((toV2 (Z - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (X - Y)) ∧ Par (toV2 (W - Y)) (Graph.rot (D.model.angleAt 1) (toV2 (X - Y)))) ∨
       (toV2 (X - Y) = Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (Z - Y)) ∧ Par (toV2 (W - Y)) (Graph.rot (D.model.angleAt 0) (toV2 (Z - Y))))) := by
    intro hc
    have hP : PF (c0' + 1 + 1) := by
      rcases hc with hc | hc
      · rw [show c0' + 1 + 1 = b0 by omega]; exact hPFb
      · rw [show c0' + 1 + 1 = b0 + 6 by omega]; exact (hPF6 b0).2 hPFb
    obtain ⟨W, hW, T, hT, hTe⟩ := final (c0' + 1) hQFc hP
    have hlb' : ℓ (c0' + 1 + 1) = 1 := by
      rcases hc with hc | hc
      · rw [show c0' + 1 + 1 = b0 by omega]; exact hlb
      · rw [show c0' + 1 + 1 = b0 + 6 by omega, hperL]; exact hlb
    have hs : s (c0' + 1 + 2) = s (b0 + 1) := by
      rcases hc with hc | hc
      · rw [show c0' + 1 + 2 = b0 + 1 by omega]
      · rw [show c0' + 1 + 2 = b0 + 1 + 6 by omega, hperS]
    have h2 := rv (c0' + 1) 2
    have h1r := rv (c0' + 1) 1
    rw [hs] at h2
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h2
    rw [Finset.sum_range_succ, Finset.sum_range_zero] at h1r
    simp only [zero_add, add_zero, hwdl, hlc1, hlb'] at h2 h1r
    refine ⟨W, hW, Or.inr ⟨?_, ?_⟩⟩
    · have h2' : Par (toV2 (X - Y)) (Graph.rot (D.model.angleAt 0 + D.model.angleAt 1) (toV2 (Z - Y))) :=
        hXu.symm.trans (h2.trans (par_rot _ hZu))
      exact eq_of_par_nsq h2' (by rw [nsq_rot]; exact hnorm.symm)
    · rw [hTe]
      exact par_smul_pos hT (h1r.trans (par_rot _ hZu))
  rcases comb_B ℓ hperL hc0 hc1 hnt hb0 hc0' ⟨hlb, hlb1⟩ ⟨hlc, hlc1⟩ with h | h
  · exact caseA h
  · exact caseB h

#print axioms gexc_start_dir

end Erdos634.Draft.LaczFormal.RG
