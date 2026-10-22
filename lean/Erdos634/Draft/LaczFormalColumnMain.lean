import Erdos634.Draft.LaczFormalColumnZA3

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJMain` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable (F : WFrame D e f α β γ p q r)

/-- **Claims Z and A**, by descending induction on `m - s'`. -/
theorem ZA {H m lv : ℕ} (E : F.Env H m lv) :
    ∀ d s' : ℕ, s' + d = m →
      (s' + 1 ≤ m → F.Std lv m s' →
        F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1)) → False) ∧
      (F.Std lv m s' → F.FarB m lv s' → False) := by
  intro d
  induction d with
  | zero =>
    intro s' hs'
    have : s' = m := by omega
    subst this
    refine ⟨fun h => by omega, fun hStd hFar => F.Abase E hStd hFar⟩
  | succ d ih =>
    intro s' hs'
    obtain ⟨IHZ', IHA'⟩ := ih (s' + 1) (by omega)
    have hc : (((s' + 1 : ℕ) : ℝ) + 1) = (s' : ℝ) + 1 + 1 := by push_cast; ring
    have IHZ : s' + 2 ≤ m → F.Std lv m (s' + 1) →
        F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv ((s' : ℝ) + 1 + 1)) → False := by
      intro h2 hStd1 hstr
      exact IHZ' (by omega) hStd1 (by rw [hc]; exact hstr)
    exact ⟨fun hs hStd hpass => F.Zstep E hs hStd hpass IHZ,
      fun hStd hFar => F.Astep E (by omega) hStd hFar IHZ IHA'⟩

/-- **The down-tile rule `T(m)`**, from the rules `T(i)`, `A(i)` for `i < m`. -/
theorem Tmain {H m : ℕ} (hB : F.Bnd H) (IHT : ∀ i, i < m → F.TRule H i) (IHA : ∀ i, i < m → F.ARule H i) :
    F.TRule H m := by
  classical
  intro lv hlv hrH hme hG hups
  have hnsJ := F.ns_J hB hlv hrH hG (hups m le_rfl)
  have E : F.Env H m lv := ⟨hB, hrH, hme, IHT, IHA, hnsJ⟩
  -- Step A: the down tiles between the `m+1` up tiles
  have hDn : ∀ x : ℕ, x + 1 ≤ m → F.DownCell (x : ℝ) (lv : ℝ) := by
    intro x hx
    have h0 : x < m := by omega
    have h1 : lv + x + 1 ≤ H := by omega
    have h2 : x + 1 ≤ e := by omega
    have h3 : F.Ground lv (x + 1) := WFrame.Ground.mono F hG (by omega)
    have h4 : ∀ x'' : ℕ, x'' ≤ x → F.UpCell (x'' : ℝ) (lv : ℝ) := fun x'' hx'' => hups x'' (by omega)
    have h5 : F.TRule H x := IHT x h0
    exact h5 lv hlv h1 h2 h3 h4
  have hStd0 : F.Std lv m 0 := by
    intro t ht
    have : t = 0 := by omega
    subst this
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simpa using hups x (by omega)
    · simpa using hDn x (by omega)
  have hJ0 : F.Dp m lv ((0 : ℕ) : ℝ) = F.pt ((m : ℝ) + 1) (lv : ℝ) := by
    unfold Dp; simp
  -- nothing straddles `D_1`
  have hnsD1 : ¬ F.StrL ((m : ℝ) + 1) (lv : ℝ) (F.Dp m lv (((0 : ℕ) : ℝ) + 1)) := by
    by_cases hm : 1 ≤ m
    · intro hstr
      exact (F.ZA E m 0 (by omega)).1 hm hStd0 hstr
    · have hm0 : m = 0 := by omega
      subst hm0
      have := F.ns_Dend 0 lv hB hrH
      simpa using this
  obtain ⟨-, hcov⟩ := F.lcov (s' := 0) E (by omega) hStd0 hnsD1
  obtain ⟨e', he', hends⟩ := hcov 0 (by omega)
  obtain ⟨hvt, hcF⟩ := chain_tileVerts he' (A := F.Dp m lv ((0 : ℕ) : ℝ)) (B := F.Dp m lv (((0 : ℕ) : ℝ) + 1))
    (by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩)
  have hd := F.dist_Dp m lv ((0 : ℕ) : ℝ)
  rcases tv_bedge F.S hvt hd with ⟨h1, h2, -, -, -⟩ | ⟨h1, h2, -, -, -⟩
  · -- type A: impossible by Claim A
    exfalso
    exact (F.ZA E m 0 (by omega)).2 hStd0 ⟨e'.1, _, hvt, hcF, h2⟩
  · -- type B: the standard down tile
    rw [hJ0] at hvt h1
    have hD1 : F.Dp m lv (((0 : ℕ) : ℝ) + 1) = F.pt (m : ℝ) ((lv : ℝ) + 1) := by
      unfold Dp; congr 1 <;> simp
    rw [hD1] at hvt
    have hu : F.pt (m : ℝ) ((lv : ℝ) + 1) - F.pt ((m : ℝ) + 1) (lv : ℝ) = F.v - F.e0 := by
      rw [F.pt_sub]; module
    have hZc : cross (F.v - F.e0) ((D.tile e'.1).pts (e'.2 + 2)) ≤
        cross (F.v - F.e0) (F.pt ((m : ℝ) + 1) (lv : ℝ)) := by
      have := hcF (e'.2 + 2)
      simpa [crossL_apply] using this
    have hcr := tv_cross_ne hvt
    rw [hu] at hcr
    have hside : cross (F.pt (m : ℝ) ((lv : ℝ) + 1) - F.pt ((m : ℝ) + 1) (lv : ℝ))
        ((D.tile e'.1).pts (e'.2 + 2) - F.pt ((m : ℝ) + 1) (lv : ℝ)) < 0 := by
      rw [hu]
      have : cross (F.v - F.e0) ((D.tile e'.1).pts (e'.2 + 2) - F.pt ((m : ℝ) + 1) (lv : ℝ)) ≤ 0 := by
        rw [cross_sub_right]; linarith
      exact lt_of_le_of_ne this hcr
    have hZ := F.third_down (x := (m : ℝ)) (y := (lv : ℝ)) hvt h1 hside
    exact ⟨e'.1, by rw [hZ] at hvt; exact hvt⟩

/-- The `e0`-coordinate of a point. -/
noncomputable def xc (z : Plane) : ℝ := cross (z - F.O) F.v / cross F.e0 F.v

theorem xc_pt (x y : ℝ) : F.xc (F.pt x y) = x := by
  unfold xc
  have : F.pt x y - F.O = x • F.e0 + y • F.v := by simp only [pt]; abel
  rw [this, cross_add_left_, cross_smul_left_, cross_smul_left_, Erdos634.Geometry.cross_self]
  field_simp [F.hcr.ne']
  ring

theorem xc_add_e0 (z : Plane) (t : ℝ) : F.xc (z + t • F.e0) = F.xc z + t := by
  unfold xc
  rw [add_sub_right_comm, cross_add_left_, cross_smul_left_, add_div]
  field_simp [F.hcr.ne']

theorem ht_add_e0 (z : Plane) (t : ℝ) : F.ht (z + t • F.e0) = F.ht z := by
  unfold ht
  rw [add_sub_right_comm, cross_add_right, cross_smul_right, Erdos634.Geometry.cross_self]; simp

/-- A tile with a vertex `K = J + t e0` (`t > 0`) is neither the up tile `(m, lv)` nor the down tile `(m, lv)`. -/
theorem Y_ne_up {i iA : Fin N} {m lv : ℕ} {K Z : Plane} {t : ℝ} (ht : 0 < t)
    (hv : TileVerts (D.tile i) (F.pt ((m : ℝ) + 1) (lv : ℝ)) K Z)
    (hK : K = F.pt ((m : ℝ) + 1) (lv : ℝ) + t • F.e0)
    (hiA : TileVerts (D.tile iA) (F.pt (m : ℝ) (lv : ℝ)) (F.pt ((m : ℝ) + 1) (lv : ℝ)) (F.pt (m : ℝ) ((lv : ℝ) + 1))) :
    i ≠ iA := by
  intro h
  subst h
  obtain ⟨k, hk⟩ := hv.vertex_B
  have hx : F.xc K = (m : ℝ) + 1 + t := by rw [hK, F.xc_add_e0, F.xc_pt]
  have hh : F.ht K = (lv : ℝ) := by rw [hK, F.ht_add_e0, F.ht_pt]
  rcases hiA.pts_mem k with h0 | h0 | h0
  · rw [hk] at h0
    have := congrArg F.xc h0
    rw [F.xc_pt] at this; linarith
  · rw [hk] at h0
    have := congrArg F.xc h0
    rw [F.xc_pt] at this; linarith
  · rw [hk] at h0
    have := congrArg F.ht h0
    rw [F.ht_pt] at this; linarith

theorem Y_ne_down {i iD : Fin N} {m lv : ℕ} {K Z : Plane} {t : ℝ} (ht : 0 < t)
    (hv : TileVerts (D.tile i) (F.pt ((m : ℝ) + 1) (lv : ℝ)) K Z)
    (hK : K = F.pt ((m : ℝ) + 1) (lv : ℝ) + t • F.e0)
    (hiD : TileVerts (D.tile iD) (F.pt ((m : ℝ) + 1) (lv : ℝ)) (F.pt (m : ℝ) ((lv : ℝ) + 1))
      (F.pt ((m : ℝ) + 1) ((lv : ℝ) + 1))) :
    i ≠ iD := by
  intro h
  subst h
  obtain ⟨k, hk⟩ := hv.vertex_B
  have hx : F.xc K = (m : ℝ) + 1 + t := by rw [hK, F.xc_add_e0, F.xc_pt]
  have hh : F.ht K = (lv : ℝ) := by rw [hK, F.ht_add_e0, F.ht_pt]
  rcases hiD.pts_mem k with h0 | h0 | h0
  · rw [hk] at h0
    have := congrArg F.xc h0
    rw [F.xc_pt] at this; linarith
  · rw [hk] at h0
    have := congrArg F.ht h0
    rw [F.ht_pt] at this; linarith
  · rw [hk] at h0
    have := congrArg F.ht h0
    rw [F.ht_pt] at this; linarith

/-- **The rule `A(m)`**, from the down-tile rule `T(m)`. -/
theorem Amain {H m : ℕ} (hB : F.Bnd H) (hT : F.TRule H m) : F.ARule H m := by
  classical
  intro lv hlv hrH hme hG hups i K Z t hv hK ht hdist hup hne
  obtain ⟨iD, hiD⟩ := hT lv hlv hrH hme hG hups
  obtain ⟨iA, hiA⟩ := hups m le_rfl
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct F.S
  have hHr : (lv : ℝ) + m + 1 ≤ H := by exact_mod_cast hrH
  have hγD : (D.tile iD).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = γ := (F.down_angles hiD).1
  have hαA : (D.tile iA).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = α := (F.up_angles hiA).2.1
  -- the angle of `Y` at `J` is `α` or `γ`
  have hY : (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = α ∨
      (D.tile i).localAngle (F.pt ((m : ℝ) + 1) (lv : ℝ)) = γ := by
    rcases hdist with hb | hc
    · rcases tv_bedge F.S hv hb with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · rcases tv_cedge F.S hv hc with h | h
      · exact Or.inl h.1
      · exact absurd h.1 hne
  have hiAD : iA ≠ iD := by
    intro h
    rw [h] at hαA
    rw [hγD] at hαA
    exact hαγ.symm hαA
  have hiYA : i ≠ iA := F.Y_ne_up ht hv hK hiA
  have hiYD : i ≠ iD := F.Y_ne_down ht hv hK hiD
  have hZht : (lv : ℝ) < F.ht Z := by
    have e2 : F.ht Z - (lv : ℝ) = cross F.e0 (Z - F.pt ((m : ℝ) + 1) (lv : ℝ)) / cross F.e0 F.v := by
      have := F.ht_sub Z (F.pt ((m : ℝ) + 1) (lv : ℝ)); rwa [F.ht_pt] at this
    have : 0 < F.ht Z - (lv : ℝ) := by rw [e2]; exact div_pos hup F.hcr
    linarith
  have hnbY : ¬ F.Below (lv : ℝ) i := F.not_below_of_TV hv hZht
  have hnbA : ¬ F.Below (lv : ℝ) iA := F.not_below_of_TV hiA (by rw [F.ht_pt]; linarith)
  have hnbD : ¬ F.Below (lv : ℝ) iD := F.not_below_of_TV hiD (by rw [F.ht_pt]; linarith)
  have cA := cnt_ge_one hαA
  have cD := cnt_ge_one hγD
  -- an interior point, with the three tiles of the ground below
  obtain ⟨lv0, rfl⟩ : ∃ lv0, lv = lv0 + 1 := ⟨lv - 1, by omega⟩
  obtain ⟨iγ, iβ, iα, hγ, hβ, hα, hbγ, hbβ, hbα⟩ :=
    F.ground_junction (ρ := lv0) (k := m + 1) (x := m + 1) hG (by omega) le_rfl
  have hJc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hcast : (((lv0 + 1 : ℕ)) : ℝ) = (lv0 : ℝ) + 1 := by push_cast; ring
  rw [hJc] at hγ hβ hα
  rw [hcast] at hγD hαA hY
  have hint : F.pt ((m : ℝ) + 1) ((lv0 : ℝ) + 1) ∈ interior D.target.carrier := by
    apply F.pt_interior (by linarith) (by positivity)
    exact (F.latOK hB (by linarith) (by positivity) (by rw [hcast] at hHr; linarith)).2.2
  have hbγ' : F.Below ((lv0 + 1 : ℕ) : ℝ) iγ := hbγ
  have hbα' : F.Below ((lv0 + 1 : ℕ) : ℝ) iα := hbα
  have hne1 : iα ≠ iA := fun h => hnbA (h ▸ hbα')
  have hne2 : iα ≠ i := fun h => hnbY (h ▸ hbα')
  have hne3 : iγ ≠ iD := fun h => hnbD (h ▸ hbγ')
  have hne4 : iγ ≠ i := fun h => hnbY (h ▸ hbγ')
  have hfig := ifig F.S hint
  rcases hY with h | h
  · have c1 := cnt_ge_three hne1 hne2 hiYA.symm hα hαA h
    have c2 := cnt_ge_two hne3 hγ hγD
    omega
  · have c1 := cnt_ge_three hne3 hne4 hiYD.symm hγ hγD h
    have c2 := cnt_ge_two hne1 hα hαA
    omega

/-- **The induction `M(j)`**: for every `m`, the down-tile rule `T(m)` and the rule `A(m)` hold at all levels `lv ≥ 1` (a wall frame has no level 0). -/
theorem MJ_main {H : ℕ} (hB : F.Bnd H) : ∀ m, F.TRule H m ∧ F.ARule H m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hT : F.TRule H m := F.Tmain hB (fun i hi => (ih i hi).1) (fun i hi => (ih i hi).2)
    exact ⟨hT, F.Amain hB hT⟩


end WFrame

end Erdos634.LaczCol
