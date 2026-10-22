import Erdos634.Draft.LaczFormalColumnBits

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJZ` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable (F : WFrame D e f α β γ p q r)

theorem u_ne : F.v - F.e0 ≠ 0 := by
  intro h
  have : ‖F.v - F.e0‖ = 0 := by rw [h, norm_zero]
  rw [F.hu] at this
  have hb : (0 : ℝ) < tb e f := by exact_mod_cast b_pos e f F.S.he F.S.hef
  linarith

theorem crossL_u_ne : (crossL (F.v - F.e0) : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
  intro h
  apply F.u_ne
  apply eq_zero_of_cross_eq_zero
  intro w
  have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h
  simpa using this

/-- A straddled point carries a tile with a straight angle. -/
theorem straddled_pi {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {y : Plane}
    (h : Straddled D.toDissection g c y) : ∃ i : Fin N, (D.tile i).localAngle y = Real.pi := by
  obtain ⟨e', -, hy⟩ := h
  exact ⟨e'.1, localAngle_pi_of_openSegment (D.tile e'.1) e'.2 hy⟩

theorem ns_J {H m lv : ℕ} (hB : F.Bnd H) (hlv : 1 ≤ lv) (hrH : lv + m + 1 ≤ H) (hG : F.Ground lv (m + 1))
    (hA : F.UpCell (m : ℝ) (lv : ℝ)) :
    ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.pt ((m : ℝ) + 1) (lv : ℝ)) := by
  classical
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  intro hstr
  obtain ⟨lv0, rfl⟩ : ∃ lv0, lv = lv0 + 1 := ⟨lv - 1, by omega⟩
  obtain ⟨iγ, iβ, iα, hγ, hβ, hα, hbγ, hbβ, hbα⟩ :=
    F.ground_junction (ρ := lv0) (k := m + 1) (x := m + 1) hG (by omega) le_rfl
  obtain ⟨iπ, hπ⟩ := WFrame.straddled_pi hstr
  obtain ⟨iA, hiA, hbA⟩ := F.up_below hA
  have hJc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hJc] at hγ hβ hα
  have hcast : (((lv0 + 1 : ℕ)) : ℝ) = (lv0 : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hπ hstr
  have hAα : (D.tile iA).localAngle (F.pt ((m : ℝ) + 1) ((lv0 : ℝ) + 1)) = α := by
    have := (F.up_angles hiA).2.1
    rwa [hcast] at this
  -- iA is not below
  have hnb : ¬ F.Below ((lv0 + 1 : ℕ) : ℝ) iA := F.not_below_of_TV hiA (by rw [F.ht_pt]; linarith)
  have hne : iA ≠ iα := fun h => hnb (h ▸ hbα)
  have hint : F.pt ((m : ℝ) + 1) ((lv0 : ℝ) + 1) ∈ interior D.target.carrier := by
    apply F.pt_interior (by linarith) (by positivity)
    exact (F.latOK hB (by linarith) (by positivity) (by linarith)).2.2
  have h1 := cnt_ge_two hne hAα hα
  have h2 := cnt_ge_one hγ
  have h3 := cnt_ge_one hπ
  have := ifig F.S hint
  omega


end WFrame

end Erdos634.LaczCol
