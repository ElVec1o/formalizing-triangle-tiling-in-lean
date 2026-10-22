import Erdos634.Draft.LaczFormalMJZ

/-!
# The stage tiles at `D_s`, and a far edge through `D_s` lies inside `[J, D_{s+1}]` (rule `M(j)`)

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

/-- An edge of the far chain straddling `X + s•u` (`s > 0`) lies inside `[X, X + t•u]` when neither `X` nor
`X + t•u` (`t > s`) is straddled. -/
theorem edge_inside_of_ns {D : Dissection N} {X u : Plane} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hf : f ≠ 0)
    (hX : f X = c) (hu : f u = 0) (hu0 : u ≠ 0) {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) {s t : ℝ}
    (hs0 : 0 < s) (hst : s < t)
    (hmem : X + s • u ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    (h0 : ¬ Straddled D f c X) (ht : ¬ Straddled D f c (X + t • u)) :
    (D.tile e.1).edge e.2 ⊆ segment ℝ X (X + t • u) := by
  classical
  obtain ⟨h0e, h1e⟩ := onLine (D := D) (f := f) (g := f) (c := c) (d := c) (fun _ => Iff.rfl) he
  obtain ⟨hlt, hedge, hopen, -⟩ := edge_data (D := D) hf hX hu hu0 h0e h1e
  rw [hopen] at hmem
  obtain ⟨x, hx, hxs⟩ := hmem
  have hxs' : x = s := lm_injective hu0 hxs
  subst hxs'
  have hlo : 0 ≤ lo D X u e := by
    by_contra h
    push Not at h
    apply h0
    have := (str_iff (D := D) (fun _ => Iff.rfl) hf hX hu hu0 0).mpr ⟨e, he, h, lt_trans hs0 hx.2⟩
    simpa using this
  have hhi : hi D X u e ≤ t := by
    by_contra h
    push Not at h
    apply ht
    exact (str_iff (D := D) (fun _ => Iff.rfl) hf hX hu hu0 t).mpr ⟨e, he, lt_trans hx.1 hst, h⟩
  have := (inside_iff (D := D) (fun _ => Iff.rfl) hf hX hu hu0 he (s := 0) (t := t) (by linarith)).mpr ⟨hlo, hhi⟩
  rwa [zero_smul, add_zero] at this

namespace LFrame

variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : LFrame D e f α β γ p q r)

/-- The up tile `N_{s'+1}` with top vertex `D_{s'+1}`: `γ` there, a vertex on the near side of `l`. -/
theorem stage_N {m lv s' : ℕ} (hStd : F.Std lv m s') (hs' : s' + 1 ≤ m + 1) :
    ∃ (iN : Fin N) (A B : Plane), TileVerts (D.tile iN) A B (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1))) ∧
      B = F.pt ((m : ℝ) + 1 - (s' : ℝ)) ((lv : ℝ) + (s' : ℝ)) ∧
      (D.tile iN).localAngle (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1))) = γ ∧
      cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) < cross (F.v - F.e0) A ∧
      F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iN := by
  obtain ⟨hU, -⟩ := hStd s' le_rfl
  obtain ⟨iN, hiN⟩ := hU (m - s') (by omega)
  have hx : ((m - s' : ℕ) : ℝ) = (m : ℝ) - s' := by rw [Nat.cast_sub (by omega)]
  rw [hx] at hiN
  have hang := (F.up_angles hiN).2.2
  have hbel : F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iN :=
    F.below_of_verts hiN (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith)
  have pA : F.pt ((m : ℝ) - s') ((lv : ℝ) + s') =
      F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + s') := by congr 1; ring
  have pB : F.pt ((m : ℝ) - s' + 1) ((lv : ℝ) + s') = F.pt ((m : ℝ) + 1 - (s' : ℝ)) ((lv : ℝ) + (s' : ℝ)) := by
    congr 1; ring
  have pC : F.pt ((m : ℝ) - s') ((lv : ℝ) + s' + 1) =
      F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1)) := by congr 1 <;> ring
  rw [pA, pB, pC] at hiN
  rw [pC] at hang
  refine ⟨iN, _, _, hiN, rfl, hang, ?_, ?_⟩
  · have e1 : F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + s') - F.pt ((m : ℝ) + 1) (lv : ℝ) =
        (s' : ℝ) • (F.v - F.e0) - F.e0 := by
      rw [F.pt_sub]; module
    have : cross (F.v - F.e0) (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + s')) -
        cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) = cross F.e0 F.v := by
      rw [← cross_sub_right, e1, cross_sub_right, cross_smul_right, Erdos634.Geometry.cross_self]
      simp only [cross, PiLp.sub_apply]; ring
    linarith [F.hcr]
  · exact hbel

/-- The down tile with top-right vertex `D_{s'+1}`: `β` there. -/
theorem stage_D {m lv s' : ℕ} (hStd : F.Std lv m s') (hs : s' + 1 ≤ m) :
    ∃ iD : Fin N, (D.tile iD).localAngle (F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1))) = β ∧
      F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iD := by
  obtain ⟨-, hD⟩ := hStd s' le_rfl
  obtain ⟨iD, hiD⟩ := hD (m - s' - 1) (by omega)
  have hx : ((m - s' - 1 : ℕ) : ℝ) = (m : ℝ) - s' - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hx] at hiD
  have hang := (F.down_angles hiD).2.2
  have hbel : F.Below ((lv : ℝ) + ((s' : ℝ) + 1)) iD :=
    F.below_of_verts hiD (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith) (by rw [F.ht_pt]; linarith)
  have pC : F.pt ((m : ℝ) - s' - 1 + 1) ((lv : ℝ) + s' + 1) =
      F.pt ((m : ℝ) + 1 - ((s' : ℝ) + 1)) ((lv : ℝ) + ((s' : ℝ) + 1)) := by congr 1 <;> ring
  rw [pC] at hang
  exact ⟨iD, hang, hbel⟩

end LFrame

end Erdos634.LaczMJ
