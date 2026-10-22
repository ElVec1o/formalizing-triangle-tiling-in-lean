import Erdos634.Draft.LaczFormalColumnStage2

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJAdv` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable (F : WFrame D e f α β γ p q r)

theorem adv {H m lv s : ℕ} (hB : F.Bnd H) (hrH : lv + m + 1 ≤ H) (hme : m + 1 ≤ e)
    (hs1 : 1 ≤ s) (hsm : s ≤ m)
    (IHT : ∀ i, i < m → F.TRule H i) (IHA : ∀ i, i < m → F.ARule H i)
    (hStd : F.Std lv m (s - 1))
    (hns : ¬ F.StrH ((lv : ℝ) + s) (F.pt ((m : ℝ) + 1 - s) ((lv : ℝ) + s))) :
    F.Std lv m s := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  have hcov := F.h_cover hB hrH hme hs1 hsm hStd hns
  obtain ⟨n', hn'⟩ : ∃ n', n' = m + 1 - s := ⟨_, rfl⟩
  have hn'r : (n' : ℝ) = (m : ℝ) + 1 - s := by
    rw [hn', Nat.cast_sub (by omega)]; push_cast; ring
  set ρ : ℝ := (lv : ℝ) + s with hρ
  have hcastρ : ((lv + s : ℕ) : ℝ) = ρ := by rw [hρ]; push_cast; ring
  have hrow : ∀ x : ℕ, x < n' → ∃ (i : Fin N) (Z : Plane),
      TileVerts (D.tile i) (F.pt (x : ℝ) ρ) (F.pt ((x : ℝ) + 1) ρ) Z ∧
        ∀ j, ρ ≤ F.ht ((D.tile i).pts j) := by
    intro x hx
    obtain ⟨e', he', hends⟩ := hcov (n' - 1 - x) (by omega)
    have hk : (((n' - 1 - x : ℕ)) : ℝ) = (n' : ℝ) - 1 - x := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have p1 : (m : ℝ) + 1 - s - ((n' - 1 - x : ℕ) : ℝ) = (x : ℝ) + 1 := by rw [hk, hn'r]; ring
    rw [p1] at hends
    simp only [add_sub_cancel_right] at hends
    have := chain_tileVerts he' (A := F.pt (x : ℝ) ρ) (B := F.pt ((x : ℝ) + 1) ρ) (by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩)
    exact ⟨_, _, this.1, F.chainH_ht this.2⟩
  have hU' : ∀ x : ℕ, x + (s - 1) ≤ m → F.UpCell (x : ℝ) ((lv : ℝ) + ((s - 1 : ℕ) : ℝ)) :=
    fun x hx => (hStd (s - 1) le_rfl).1 x hx
  have hD' : ∀ x : ℕ, x + (s - 1) + 1 ≤ m → F.DownCell (x : ℝ) ((lv : ℝ) + ((s - 1 : ℕ) : ℝ)) :=
    fun x hx => (hStd (s - 1) le_rfl).2 x hx
  have hGr : ∀ k : ℕ, k + s ≤ m → F.Ground (lv + s) k := fun k hk => F.ground_of_rows hs1 hk hU' hD'
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hup : ∀ x : ℕ, x < n' → F.UpCell (x : ℝ) ρ := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      intro hx
      obtain ⟨i, Z, hv, hge⟩ := hrow x hx
      have hup0 := F.third_above hv hge
      have hZht : ρ < F.ht Z := by
        have e2 : F.ht Z - ρ = cross F.e0 (Z - F.pt (x : ℝ) ρ) / cross F.e0 F.v := by
          have := F.ht_sub Z (F.pt (x : ℝ) ρ); rwa [F.ht_pt] at this
        have : 0 < F.ht Z - ρ := by rw [e2]; exact div_pos hup0 F.hcr
        linarith
      have hnb : ¬ F.Below ρ i := F.not_below_of_TV hv hZht
      have hβ : (D.tile i).localAngle (F.pt (x : ℝ) ρ) = β := by
        rcases tv_cedge F.S hv (F.dist_pt_c x ρ) with h | h
        · exfalso
          have hα := h.1
          rcases Nat.eq_zero_or_pos x with rfl | hxpos
          · -- the leg point
            obtain ⟨ρ0, hρ0⟩ : ∃ ρ0, lv + s = ρ0 + 1 := ⟨lv + s - 1, by omega⟩
            have hG0 := hGr 0 (by omega)
            rw [hρ0] at hG0
            have hρc : (ρ0 : ℝ) + 1 = ρ := by rw [hρ]; exact_mod_cast hρ0.symm
            have hmu' : (ρ0 : ℝ) + 1 < F.mu := by
              rw [hρc, hρ]
              have : (s : ℝ) ≤ m := by exact_mod_cast hsm
              linarith [F.hmu, hB.2]
            obtain ⟨c1, -, -, -⟩ := F.leg_fig hG0 hmu'
            obtain ⟨iγ, iα, hγ, hα', hbγ, hbα, -, hsα⟩ := F.ground_leg_side hG0 hmu'
            rw [hρc] at hα'
            have hbα' : F.Below ρ iα := by rw [← hρc]; simpa using hbα
            have hne : i ≠ iα := fun h => hnb (h ▸ hbα')
            have hα0 : (D.tile i).localAngle (F.pt 0 ρ) = α := by simpa using hα
            have hρpos : (0 : ℝ) < ρ := by rw [← hρc]; positivity
            have hρmu : ρ < F.mu := by rw [← hρc]; exact hmu'
            have hsi : i ∈ Side D.toDissection F.wg F.wc :=
              F.tile_mem_Side hρpos hρmu (x' := 1) (y' := ρ) one_pos
                (by simpa using hv.vertex_A) (by simpa using hv.vertex_B)
            rw [hρc] at c1
            have := scnt_ge_two hne hsi hsα hα0 hα'
            omega
          · -- `A(x-1)` at the level `lv + s`
            obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
            have hx'm : x' < m := by omega
            have hxc : ((x' + 1 : ℕ) : ℝ) = (x' : ℝ) + 1 := by push_cast; ring
            rw [hxc] at hv hα hup0
            refine IHA x' hx'm (lv + s) (by omega) (by omega) (by omega) (hGr (x' + 1) (by omega))
              (fun x'' hx'' => ?_) i (F.pt ((x' : ℝ) + 1 + 1) ρ) Z 1 ?_ ?_ one_pos ?_ ?_ ?_
            · have := ih x'' (by omega) (by omega)
              rwa [hcastρ]
            · rw [hcastρ]; exact hv
            · simp only [pt, one_smul]; module
            · exact Or.inr (by rw [hcastρ]; exact F.dist_pt_c _ _)
            · rw [hcastρ]; exact hup0
            · rw [hcastρ, hα]; exact hαβ
        · exact h.1
      have hZ := F.third_up hv hβ hup0
      exact ⟨i, by rw [hZ] at hv; exact hv⟩
  have hdn : ∀ x : ℕ, x + s + 1 ≤ m → F.DownCell (x : ℝ) ρ := by
    intro x hx
    have := IHT x (by omega) (lv + s) (by omega) (by omega) (by omega) (hGr (x + 1) (by omega))
      (fun x'' hx'' => by
        have := hup x'' (by omega)
        rwa [hcastρ])
    rwa [hcastρ] at this
  intro t ht
  by_cases hts : t ≤ s - 1
  · exact hStd t hts
  · have : t = s := by omega
    subst this
    exact ⟨fun x hx => hup x (by omega), fun x hx => hdn x hx⟩


end WFrame

end Erdos634.LaczCol
