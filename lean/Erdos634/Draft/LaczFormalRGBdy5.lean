-- Draft/LaczFormalRGBdy5.lean -- S4 of PLAN_THM21: Laczkovich Lemma 9.1 (iii) along an edge: if the first or the last tile side of the walk along an edge of the polygon has length `a`, all
-- of them do, so the edge has length `k a` (`k` the number of tiles of the walk).  (`gamma = pi/2`.)
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 9.1 (iii)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGBdy4

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- The standing hypotheses of the boundary/graph lemmas: distance- and angle-matching `idx`, `a` not a nonnegative rational combination of `b, c`, and the parity
hypothesis `HalfPar` (even number of non-`α` corners at vertices with corner-angle sum `π`). -/
structure CaseG (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hnc : NotComb (slen D 0) (slen D 1) (slen D 2)
  hhp : HalfPar D idx

theorem CaseG.hab {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseG D idx) : slen D 0 ≠ slen D 1 := by
  intro e
  have := h.hnc 1 1 0 one_pos
  apply this; rw [e]; simp

theorem CaseG.hac {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseG D idx) : slen D 0 ≠ slen D 2 := by
  intro e
  have := h.hnc 1 0 1 one_pos
  apply this; rw [e]; simp

/-- The standing hypotheses of Case V (`γ = π/2`, `a` not a nonnegative rational combination of `b, c`, regular corner counts). -/
structure CaseV (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hnc : NotComb (slen D 0) (slen D 1) (slen D 2)
  hγ : D.model.angleAt 2 = Real.pi / 2
  hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1

theorem CaseV.toG {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseV D idx) : CaseG D idx :=
  ⟨h.hidx, h.hidxA, h.hnc, halfPar_of_pi2 D idx h.hγ h.hregc⟩

theorem CaseV.hab {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseV D idx) : slen D 0 ≠ slen D 1 := h.toG.hab

theorem CaseV.hac {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseV D idx) : slen D 0 ≠ slen D 2 := h.toG.hac

/-- All the steps of a walk ending at the end of an edge have the same status (length `a` or not). -/
theorem walk_status_chain (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hV : CaseG D idx) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {U Y : Plane} (hY : Y = P.v (i + 1)) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) U Y L) (hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (U - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2)) :
    ∀ e0, L.head? = some e0 → ∀ e ∈ L, (dist e.2.1 e.2.2 = slen D 0 ↔ dist e0.2.1 e0.2.2 = slen D 0) := by
  induction W with
  | nil X => intro e0 he0; simp at he0
  | @cons j X X' Y L' hS W' ih =>
    intro e0 he0 e he
    simp only [List.head?_cons, Option.some.injEq] at he0
    subst he0
    rcases List.mem_cons.mp he with h | h
    · subst h; exact Iff.rfl
    · -- e ∈ L'
      cases hL' : L' with
      | nil => rw [hL'] at h; simp at h
      | cons e2 L'' =>
        rw [hL'] at h W' ih
        -- the junction X'
        obtain ⟨s, hs0, hsX⟩ := hU
        obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hdX' : toV2 (X' - P.v i) = ((s + c) * (toV2 (P.e i)).1, (s + c) * (toV2 (P.e i)).2) := by
          have : toV2 (X' - P.v i) = ((toV2 (X' - X)).1 + (toV2 (X - P.v i)).1, (toV2 (X' - X)).2 + (toV2 (X - P.v i)).2) := by
            unfold toV2; ext <;> simp
          rw [this, hcw, hsX]; ext <;> simp <;> ring
        obtain ⟨T, hT0, hTe, hTpos⟩ := walkT_progress W'
        have hTpos' : 0 < T := hTpos (by simp)
        have hd0 : toV2 (P.e i) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
        have hvert' : ∃ j k, (D.tile j).pts k = X' := by
          obtain ⟨kk, f, g, hk, hf, -⟩ := id hS
          exact ⟨j, f, hf⟩
        have hline' : crs (toV2 (P.e i)) (toV2 (X' - P.v i)) = 0 := by
          rw [hdX']; unfold crs; simp only; ring
        obtain ⟨t, ⟨ht0, ht1⟩, hXt⟩ := vertex_on_edge D.toRegionDissection P hreg i hvert' hline'
        have hne0 : t ≠ 0 := by
          rintro rfl
          have : toV2 (X' - P.v i) = 0 := by
            rw [hXt]; unfold toV2; ext <;> simp
          rw [hdX'] at this
          have h1 : (s + c) * (toV2 (P.e i)).1 = 0 := congrArg Prod.fst this
          have h2 : (s + c) * (toV2 (P.e i)).2 = 0 := congrArg Prod.snd this
          have hsc : s + c ≠ 0 := by positivity
          apply hd0
          exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hsc) ((mul_eq_zero.mp h2).resolve_left hsc)
        have hne1 : t ≠ 1 := by
          rintro rfl
          have : toV2 (Y - X') = 0 := by
            rw [hY, hXt]; unfold toV2; ext <;> simp
          rw [hTe] at this
          have h1 : T * (toV2 (P.e i)).1 = 0 := congrArg Prod.fst this
          have h2 : T * (toV2 (P.e i)).2 = 0 := congrArg Prod.snd this
          apply hd0
          exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hTpos'.ne') ((mul_eq_zero.mp h2).resolve_left hTpos'.ne')
        have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hne0)
        have ht1' : t < 1 := lt_of_le_of_ne ht1 hne1
        -- the junction status
        have hjunc := bdy_step_status D P hreg idx hV.hidx hV.hidxA hV.hnc hV.hab hV.hac hV.hhp i ht0' ht1'
          (U1 := X) (U2 := e2.2.2) (j1 := j) (j2 := e2.1) (by rw [← hXt]; exact hS)
          (by
            have := walkT_mem_step W' e2 (by simp)
            have hX2 : e2.2.1 = X' := by
              cases W' with
              | cons _ _ => rfl
            rw [← hXt, ← hX2]; exact this)
        -- induction on the tail
        have hs' : ∃ s' : ℝ, 0 ≤ s' ∧ toV2 (X' - P.v i) = (s' * (toV2 (P.e i)).1, s' * (toV2 (P.e i)).2) := ⟨s + c, by positivity, hdX'⟩
        have ihh := ih hY hs' e2 (by simp) e h
        have hX2 : e2.2.1 = X' := by
          cases W' with
          | cons _ _ => rfl
        have hjunc' : (dist X X' = slen D 0 ↔ dist e2.2.1 e2.2.2 = slen D 0) := by
          rw [hX2, hXt]
          exact hjunc
        exact ihh.trans hjunc'.symm

end Erdos634.Draft.LaczFormal.RG
