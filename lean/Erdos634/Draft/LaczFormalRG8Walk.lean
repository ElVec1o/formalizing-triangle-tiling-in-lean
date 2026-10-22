-- Draft/LaczFormalRG8Walk.lean -- Laczkovich DCG 48 (2012), Sect. 4: a SIDE-UNIFORM walk predicate `WalkU` (left walks `WalkT` = side `true`, right walks `WalkR` = side `false`), so that the
-- proof of Lemma 4.6 is written once for both sides; positions along a line (`tau`), appending and splitting walks, covering, and the unified transition lemma `gc_trans_walk`.
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG7Trans

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- A step of a division on side `b` (`true` = left tiles, steps `U -> U'` along `d`; `false` = right tiles, steps `U' -> U` along `-d`); the triple is `(tile, U, U')` with `U` before `U'`. -/
def StepU (D : RegionDissection N) (b : Bool) (d : V2) (e : Fin N × Plane × Plane) : Prop :=
  if b then TriStep (D.tile e.1) d e.2.1 e.2.2 else TriStep (D.tile e.1) (neg2 d) e.2.2 e.2.1

inductive WalkU (D : RegionDissection N) (b : Bool) (d : V2) : Plane → Plane → List (Fin N × Plane × Plane) → Prop
  | nil (X : Plane) : WalkU D b d X X []
  | cons {i : Fin N} {X X' Y : Plane} {L : List (Fin N × Plane × Plane)} :
      StepU D b d (i, X, X') → WalkU D b d X' Y L → WalkU D b d X Y ((i, X, X') :: L)

theorem walkU_of_T {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkT D d X Y L) : WalkU D true d X Y L := by
  induction W with
  | nil X => exact WalkU.nil X
  | cons hS _ ih => exact WalkU.cons (by simpa [StepU] using hS) ih

theorem walkU_of_R {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkR D d X Y L) : WalkU D false d X Y L := by
  induction W with
  | nil X => exact WalkU.nil X
  | cons hS _ ih => exact WalkU.cons (by simpa [StepU] using hS) ih

theorem walkT_of_U {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D true d X Y L) : WalkT D d X Y L := by
  induction W with
  | nil X => exact WalkT.nil X
  | cons hS _ ih => exact WalkT.cons (by simpa [StepU] using hS) ih

theorem walkR_of_U {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D false d X Y L) : WalkR D d X Y L := by
  induction W with
  | nil X => exact WalkR.nil X
  | cons hS _ ih => exact WalkR.cons (by simpa [StepU] using hS) ih

/-- Two cases for the side. -/
theorem walkU_cases {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) :
    (b = true ∧ WalkT D d X Y L) ∨ (b = false ∧ WalkR D d X Y L) := by
  cases b
  · exact Or.inr ⟨rfl, walkR_of_U W⟩
  · exact Or.inl ⟨rfl, walkT_of_U W⟩

/-- A step is a positive multiple of `d`. -/
theorem stepU_vec {D : RegionDissection N} {b : Bool} {d : V2} {e : Fin N × Plane × Plane} (h : StepU D b d e) :
    ∃ c : ℝ, 0 < c ∧ toV2 (e.2.2 - e.2.1) = (c * d.1, c * d.2) := by
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false] at h
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    refine ⟨c, hc, ?_⟩
    have h1 := congrArg Prod.fst hcw
    have h2 := congrArg Prod.snd hcw
    simp only [toV2_sub, neg2] at h1 h2 ⊢
    ext <;> simp <;> linarith
  · simp only [StepU, if_true] at h
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    exact ⟨c, hc, hcw⟩

theorem stepU_dist {D : RegionDissection N} {b : Bool} {d : V2} {e : Fin N × Plane × Plane} (h : StepU D b d e) :
    ∃ c : ℝ, 0 < c ∧ dist e.2.2 e.2.1 = c * Real.sqrt (nsq d) := by
  obtain ⟨c, hc, hv⟩ := stepU_vec h
  exact ⟨c, hc, dist_of_toV2 hc.le hv⟩

/-- Walk parameters: `Y - X = T d` and every element has parameters `0 <= t0 < t1 <= T`. -/
theorem walkU_pos {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) :
    ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ (L ≠ [] → 0 < T) ∧
      ∀ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧ toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ 0 ≤ t0 ∧ t0 < t1 ∧ t1 ≤ T := by
  induction W with
  | nil X =>
    refine ⟨0, le_rfl, by unfold toV2; ext <;> simp, fun h => absurd rfl h, ?_⟩
    intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    obtain ⟨c, hc, hcw⟩ := stepU_vec hS
    obtain ⟨T, hT0, hT, hTp, hall⟩ := ih
    have hadd : ∀ P : Plane, ∀ t : ℝ, toV2 (P - X') = (t * d.1, t * d.2) → toV2 (P - X) = ((t + c) * d.1, (t + c) * d.2) := by
      intro P t hP
      have h1 := congrArg Prod.fst hP
      have h2 := congrArg Prod.snd hP
      have h3 := congrArg Prod.fst hcw
      have h4 := congrArg Prod.snd hcw
      simp only [toV2_sub] at h1 h2 h3 h4 ⊢
      ext <;> simp <;> nlinarith
    refine ⟨T + c, by linarith, hadd Y T hT, fun _ => by linarith, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨0, c, by unfold toV2; ext <;> simp, hcw, le_rfl, hc, by linarith⟩
    · obtain ⟨t0, t1, h0, h1, h2, h3, h4⟩ := hall e he'
      exact ⟨t0 + c, t1 + c, hadd _ _ h0, hadd _ _ h1, by linarith, by linarith, by linarith⟩

theorem walkU_append {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L1 L2 : List (Fin N × Plane × Plane)} :
    WalkU D b d X Y (L1 ++ L2) ↔ ∃ M, WalkU D b d X M L1 ∧ WalkU D b d M Y L2 := by
  induction L1 generalizing X with
  | nil =>
    constructor
    · intro h; exact ⟨X, WalkU.nil X, by simpa using h⟩
    · rintro ⟨M, hM, h2⟩
      cases hM
      simpa using h2
  | cons x L1 ih =>
    obtain ⟨i, A, B⟩ := x
    constructor
    · intro h
      simp only [List.cons_append] at h
      cases h with
      | cons hS W' =>
        obtain ⟨M, h1, h2⟩ := ih.mp W'
        exact ⟨M, WalkU.cons hS h1, h2⟩
    · rintro ⟨M, hM, h2⟩
      cases hM with
      | cons hS W' =>
        simp only [List.cons_append]
        exact WalkU.cons hS (ih.mpr ⟨M, W', h2⟩)

theorem walkU_split {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L)
    {P : List (Fin N × Plane × Plane)} {e : Fin N × Plane × Plane} {Q : List (Fin N × Plane × Plane)} (h : L = P ++ e :: Q) :
    WalkU D b d X e.2.1 P ∧ WalkU D b d e.2.1 Y (e :: Q) := by
  subst h
  obtain ⟨M, h1, h2⟩ := walkU_append.mp W
  cases h2 with
  | cons hS W' => exact ⟨h1, WalkU.cons hS W'⟩

theorem walkU_head {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {e : Fin N × Plane × Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkU D b d X Y (e :: L)) : e.2.1 = X := by
  cases W with
  | cons hS W' => rfl

theorem walkU_nil_eq {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} (W : WalkU D b d X Y []) : X = Y := by
  cases W; rfl

/-- The last element ends at `Y`. -/
theorem walkU_last {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) (hL : L ≠ []) :
    ∃ e ∈ L, e.2.2 = Y := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      cases W
      exact ⟨(i, X, X'), List.mem_cons_self .., rfl⟩
    · obtain ⟨e, he, h⟩ := ih hL'
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩

theorem walkU_mem_step {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) :
    ∀ e ∈ L, StepU D b d e := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact hS
    · exact ih e h

/-- Sum of the side lengths equals the length of the segment. -/
theorem walkU_dist_sum {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) :
    (L.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
  rcases walkU_cases W with ⟨-, W'⟩ | ⟨-, W'⟩
  · exact walkT_dist_sum W'
  · exact walkR_dist_sum W'

/-- Covering by `(t0, t1]`. -/
theorem walkU_cover' {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) (hd : d ≠ 0)
    {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) :
    ∀ s : ℝ, 0 < s → s ≤ T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 < s ∧ s ≤ t1 := by
  rcases walkU_cases W with ⟨-, W'⟩ | ⟨-, W'⟩
  · exact walkT_cover' W' hT hd
  · exact walkR_cover' W' hT hd

/-- Covering by `[t0, t1)`. -/
theorem walkU_cover {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Y L) (hd : d ≠ 0)
    {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) :
    ∀ s : ℝ, 0 ≤ s → s < T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 ≤ s ∧ s < t1 := by
  rcases walkU_cases W with ⟨-, W'⟩ | ⟨-, W'⟩
  · exact walkT_cover W' hT hd
  · exact walkR_cover W' hT hd

/-- **Unified transition lemma for `Γ_c`**: consecutive elements `eA, eB` of a division on side `b` with common vertex `H`, `H` strictly inside an element `f` of a division on the
other side, with exactly one of the two sides of length `c`: an edge of `Γ_c` starts at `H`. -/
theorem gc_trans_walk (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    {b : Bool} {d : V2} {eA eB f : Fin N × Plane × Plane} {σ : ℝ}
    (hA : StepU D.toRegionDissection b d eA) (hB : StepU D.toRegionDissection b d eB) (hAB : eA.2.2 = eB.2.1)
    (hf : StepU D.toRegionDissection (!b) d f) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hH : eA.2.2 = f.2.1 + σ • (f.2.2 - f.2.1))
    (hord : (dist eA.2.1 eA.2.2 = slen D 2 ∧ dist eB.2.1 eB.2.2 ≠ slen D 2) ∨ (dist eA.2.1 eA.2.2 ≠ slen D 2 ∧ dist eB.2.1 eB.2.2 = slen D 2)) :
    ∃ H', GcEdge D eA.2.2 H' := by
  obtain ⟨iA, HA, H⟩ := eA
  obtain ⟨iB, H2, HB⟩ := eB
  obtain ⟨iS, V, V'⟩ := f
  simp only at hAB hH hord
  subst hAB
  cases b
  · simp only [StepU, Bool.false_eq_true, if_false, Bool.not_false, if_true] at hA hB hf
    exact gc_trans_right D idx h hA hB hf hσ0 hσ1 hH hord
  · simp only [StepU, if_true, Bool.not_true, Bool.false_eq_true, if_false] at hA hB hf
    exact gc_trans_left D idx h hA hB hf hσ0 hσ1 hH hord

end Erdos634.Draft.LaczFormal.RG
