import Erdos634.Draft.LaczFormalALBits

/-!
# Non-straddling at J, straddling and the figure (a-lattice)

Erdős \#634, base-`β` row, thick analogue of `M(j)` (Lemma A(j)).  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu,
Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJZ.lean` to the exchanged frame
`AF` (`e0` of length `a` along the base, `v` of length `c` along the left leg).
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace AF

variable (F : AF D e f α β γ p q r)

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

theorem ns_J {H m lv : ℕ} (hB : F.Bnd H) (hrH : lv + m + 1 ≤ H) (hG : F.Ground lv (m + 1))
    (hA : F.UpCell (m : ℝ) (lv : ℝ)) :
    ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.pt ((m : ℝ) + 1) (lv : ℝ)) := by
  classical
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases Nat.eq_zero_or_pos lv with rfl | hlv
  · intro hstr
    refine F.ns_start_y (x1 := (m : ℝ) + 1) (y1 := ((0 : ℕ) : ℝ)) (x2 := (m : ℝ)) (y2 := ((0 : ℕ) : ℝ) + 1)
      (by simp) (by simp) (crossL (F.v - F.e0)) (cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) ((0 : ℕ) : ℝ)))
      F.crossL_u_ne rfl ?_ hstr
    simp only [crossL_apply]
    have : F.pt (m : ℝ) (((0 : ℕ) : ℝ) + 1) = F.pt ((m : ℝ) + 1) ((0 : ℕ) : ℝ) + (F.v - F.e0) := by
      simp only [pt]; module
    rw [this, cross_add_right, Erdos634.Geometry.cross_self]; ring
  · intro hstr
    obtain ⟨lv0, rfl⟩ : ∃ lv0, lv = lv0 + 1 := ⟨lv - 1, by omega⟩
    obtain ⟨iγ, iβ, iα, hγ, hβ, hα, hbγ, hbβ, hbα⟩ :=
      F.ground_junction (ρ := lv0) (k := m + 1) (x := m + 1) hG (by omega) le_rfl
    obtain ⟨iπ, hπ⟩ := AF.straddled_pi hstr
    obtain ⟨iA, hiA, hbA⟩ := F.up_below hA
    have hJc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hJc] at hγ hβ hα
    have hcast : (((lv0 + 1 : ℕ)) : ℝ) = (lv0 : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hπ hstr
    have hAγ : (D.tile iA).localAngle (F.pt ((m : ℝ) + 1) ((lv0 : ℝ) + 1)) = γ := by
      have := (F.up_angles hiA).2.1
      rwa [hcast] at this
    -- iA is not below
    have hnb : ¬ F.Below ((lv0 + 1 : ℕ) : ℝ) iA := F.not_below_of_TV hiA (by rw [F.ht_pt]; linarith)
    have hne : iA ≠ iγ := fun h => hnb (h ▸ hbγ)
    have hint : F.pt ((m : ℝ) + 1) ((lv0 : ℝ) + 1) ∈ interior D.target.carrier := by
      apply F.pt_interior (by linarith) (by positivity)
      exact (F.latOK hB (by linarith) (by positivity) (by linarith)).2.2
    have h1 := cnt_ge_two hne hAγ hγ
    have h2 := cnt_ge_one hα
    have h3 := cnt_ge_one hπ
    have := ifig F.S hint
    omega

end AF

end Erdos634.LaczAL
