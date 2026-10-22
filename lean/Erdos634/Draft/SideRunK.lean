/-
Draft/SideRunK.lean -- Stage 3b of the formalization of the side theorem of room GAP3: Lemma N, the claim
`K(s, j0)` by induction on `s − j0`, and the run lemma `L_k` for every `k < n`
((private working notes, not included), sections 2-3).

* `Ctx.m_clamp_nat`, `Ctx.D_of`: the tile across the `a`-edge of `U(i,j)` is `D(i,j)` as soon as the claim holds
  for the size `i+1` and `N_i(j)` is not a tile (steps (2a), (2b) of the proof);
* `Ctx.N_five`: five tiles at `p(i,j+1)` when `N_i(j)` and `D(i−1,j+1)` are tiles;
* `Ctx.noN`: **Lemma N** (the mirror image `N_i(j)` of `U(i,j)` in its `a`-edge is not a tile), by induction on `i`;
* `Ctx.K_all`: **the claim `K(s, j0)`**, for all pairs, by induction on the size;
* `Ctx.run_dies`: **the run lemma `L_k`**, `1 ≤ k < n`: a run of `k` tiles `U(0,0), …, U(k−1,0)` with (K1) at its
  first end and (K3) at its last end does not exist.

Route: as in the written proof, except that step (2d) is dropped (Lemma N covers it; the text says so), the wedge
arguments are replaced by angle sums at the lattice points (`π + γ + γ`, `α + β + 3γ`), and "(F): a wedge of angle
`3α` is filled by tiles showing `α`" is replaced by `3α < β` (`Setup.three_alpha_lt_beta`, `n ≥ 3`).

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunRow

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.W2E1 Set

variable {N : ℕ} {D : CongruentDissection N} {n : ℕ} {α β γ L ax ay ε x : ℝ}

namespace Ctx

/-- the clamp of the `a`-edge of `U(i,j)` at `p(i+1,j)`: the side of the target (`j = 0`) or `D(i+1,j−1)` -/
theorem m_clamp_nat (C : Ctx D n α β γ L ax ay ε x) (i j : ℕ)
    (h : j = 0 ∨ (1 ≤ j ∧ DT D n ε x ((i + 1 : ℕ) : ℝ) ((j - 1 : ℕ) : ℝ))) :
    ∃ P' : Plane, GS n ε P' = -lv n ε x ((i:ℝ) + j + 1) ∧
      lp n ε x ((i:ℝ) + 1) j ∈ openSegment ℝ P' (lp n ε x i ((j:ℝ) + 1)) ∧
      ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x ((i:ℝ) + j + 1)),
        ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x ((i:ℝ) + 1) j) (lp n ε x i ((j:ℝ) + 1)) := by
  have hε := C.e2
  have hf1 := C.S.f1
  rcases h with rfl | ⟨hj1, t, hD⟩
  · simp only [Nat.cast_zero]
    exact C.m_clamp_base i
  · have hc1 : ((j - 1 : ℕ) : ℝ) = (j:ℝ) - 1 := by rw [Nat.cast_sub hj1, Nat.cast_one]
    rw [Nat.cast_add, Nat.cast_one, hc1] at hD
    have hle := hD.all (P := fun p => GS n ε p ≤ -lv n ε x ((i:ℝ) + j + 1))
      (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
    obtain ⟨k, m, j₃, hkm, -, -, hk, hm, -⟩ := hD
    exact C.m_clamp_tile hkm (by rw [hk]; exact lp_congr (by ring) rfl)
      (by rw [hm]; exact lp_congr rfl (by ring)) hle

/-- **Steps (2a), (2b)**: the tile across the `a`-edge of `U(i,j)` at `p(i+1,j)` is `D(i,j)`, if no tile gives (K3)
for the run `(i+j+1, j)` and `N_i(j)` is not a tile. -/
theorem D_of (C : Ctx D n α β γ L ax ay ε x) {i j : ℕ} (hi : i + 2 ≤ n)
    (hU1 : UT D n ε x i j) (hU2 : UT D n ε x ((i:ℝ) + 1) j)
    (hcl : j = 0 ∨ (1 ≤ j ∧ DT D n ε x ((i + 1 : ℕ) : ℝ) ((j - 1 : ℕ) : ℝ)))
    (hR : ∀ w, RhoEdge D n ε x w ((i:ℝ) + j + 1) j → False)
    (hNo : ∀ t, HasV D t (lp n ε x ((i:ℝ) + 1) j) (lp n ε x i ((j:ℝ) + 1))
      (lp n ε x ((i:ℝ) - nu n) ((j:ℝ) + 2 + nu n)) → False) : DT D n ε x i j := by
  obtain ⟨t₀, hU⟩ := hU1
  obtain ⟨t₂, hU2'⟩ := hU2
  have hb : (i:ℝ) + 2 ≤ n := by exact_mod_cast hi
  rcases C.m_next hU (Nat.cast_nonneg j) ⟨1, one_pos, hU2'.mem₂⟩ (C.m_clamp_nat i j hcl) hb with
    ⟨t, h⟩ | ⟨t, h⟩ | ⟨w, hw⟩
  · exact ⟨t, h⟩
  · exact (hNo t h).elim
  · exact (hR w hw).elim

/-- five tiles at `p(ξ+1, ζ+1)`: `D(ξ,ζ)`, `U(ξ+1,ζ)`, `N(ξ+1,ζ)`, `U(ξ,ζ+1)`, `D(ξ,ζ+1)` -/
theorem N_five (C : Ctx D n α β γ L ax ay ε x) {ξ ζ : ℝ} {t₁ t₂ tN t₄ t₆ : Fin N}
    (h1 : HasV D t₁ (lp n ε x (ξ + 1) ζ) (lp n ε x ξ (ζ + 1)) (lp n ε x (ξ + 1) (ζ + 1)))
    (h2 : HasV D t₂ (lp n ε x (ξ + 1) ζ) (lp n ε x (ξ + 1 + 1) ζ) (lp n ε x (ξ + 1) (ζ + 1)))
    (hN : HasV D tN (lp n ε x (ξ + 1 + 1) ζ) (lp n ε x (ξ + 1) (ζ + 1))
      (lp n ε x (ξ + 1 - nu n) (ζ + 2 + nu n)))
    (h4 : HasV D t₄ (lp n ε x ξ (ζ + 1)) (lp n ε x (ξ + 1) (ζ + 1)) (lp n ε x ξ (ζ + 1 + 1)))
    (h6 : HasV D t₆ (lp n ε x (ξ + 1) (ζ + 1)) (lp n ε x ξ (ζ + 1 + 1))
      (lp n ε x (ξ + 1) (ζ + 1 + 1))) : False := by
  have S := C.S
  have hε := C.e2
  have hf1 := S.f1
  have hν0 := nu_pos hf1
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ := S.alpha_lt_beta
  have hγdef := S.hA.hγdef
  have hβγ : β < γ := by linarith
  have hαγ : α < γ := by linarith
  have a1 := (D_angles S hε h1).2.2
  have a2 := (U_angles S hε h2).2.2
  have aN := (N_angles S hε hN).2
  have a4 := (U_angles S hε h4).2.1
  have a6 := (D_angles S hε h6).1
  have hleN := hN.all (P := fun p => GS n ε p ≤ -lv n ε x (ξ + 1 + ζ + 1))
    (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
  have hle6 := h6.all (P := fun p => GS n ε p ≤ -lv n ε x (ξ + 1 + ζ + 1))
    (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
  have n12 : t₁ ≠ t₂ := ne_of_angle (by rw [a1, a2]; exact hαγ.ne)
  have n1N : t₁ ≠ tN := ne_of_angle (by rw [a1, aN]; exact hαγ.ne)
  have n14 : t₁ ≠ t₄ := ne_of_angle (by rw [a1, a4]; exact hαβ.ne)
  have n16 : t₁ ≠ t₆ := ne_of_angle (by rw [a1, a6]; exact hαγ.ne)
  have n2N : t₂ ≠ tN := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GS n ε) hleN (i := k) (by rw [hk]; exact GS_gt hf1 hε (by linarith))).symm
  have n24 : t₂ ≠ t₄ := ne_of_angle (by rw [a2, a4]; exact hβγ.ne')
  have n26 : t₂ ≠ t₆ := by
    obtain ⟨k, hk⟩ := h2.idx₁
    exact (ne_of_F (GS n ε) hle6 (i := k) (by rw [hk]; exact GS_gt hf1 hε (by linarith))).symm
  have nN4 : tN ≠ t₄ := ne_of_angle (by rw [aN, a4]; exact hβγ.ne')
  have nN6 : tN ≠ t₆ := by
    obtain ⟨k, hk⟩ := h6.idx₂
    exact (hN.ne_of_vertex hk (lp_ne_eta hf1 (by linarith)) (lp_ne_eta hf1 (by linarith))
      (lp_ne_eta hf1 (by linarith))).symm
  have n46 : t₄ ≠ t₆ := ne_of_angle (by rw [a4, a6]; exact hβγ.ne)
  have h5 := five_angles_le D.toDissection (lp n ε x (ξ + 1) (ζ + 1)) n12 n1N n14 n16 n2N n24 n26
    nN4 nN6 n46
  have h2π := localAngle_le_two_pi D.target (lp n ε x (ξ + 1) (ζ + 1))
  rw [a1, a2, aN, a4, a6] at h5
  linarith

/-- **LEMMA N.**  If the rows `≤ j` of `Δ_{i+j+1}` are lattice and the claim holds for the sizes `≤ i`, the mirror
image `N_i(j)` of `U(i,j)` in its `a`-edge is not a tile. -/
theorem noN (C : Ctx D n α β γ L ax ay ε x) : ∀ i j : ℕ, i + j + 2 ≤ n →
    (∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ i + j → UT D n ε x i' j') →
    (∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ i + j → DT D n ε x i' j') →
    (∀ m' : ℕ, 1 ≤ m' → m' ≤ i → Aprop D n ε x m') →
    ∀ t, HasV D t (lp n ε x ((i:ℝ) + 1) j) (lp n ε x i ((j:ℝ) + 1))
      (lp n ε x ((i:ℝ) - nu n) ((j:ℝ) + 2 + nu n)) → False := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hij rowsU rowsD hA tN hN
    have S := C.S
    have hε := C.e2
    have hf1 := S.f1
    have hν0 := nu_pos hf1
    obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · -- `i = 0`: `U(0,j)`, `N_0(j)` and `φ_j` at `p(0,j+1)`
      subst hi0
      rw [Nat.cast_zero] at hN
      obtain ⟨tU, hUt⟩ := rowsU 0 j le_rfl le_rfl
      rw [Nat.cast_zero] at hUt
      obtain ⟨φ, hφc, hφπ, hφpush⟩ := C.phi (j := j + 1) (by omega) (by omega)
        (fun j' hj' => by
          have h := rowsU 0 j' (by omega) (by omega)
          rwa [Nat.cast_zero] at h)
      simp only [Nat.cast_add, Nat.cast_one] at hφπ
      have aU := (U_angles S hε hUt).2.2
      have aN := (N_angles S hε hN).2
      have hleN := hN.all (P := fun p => GS n ε p ≤ -lv n ε x (0 + (j:ℝ) + 1))
        (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
      have hφU : φ ≠ tU := ne_of_angle (by rw [hφπ, aU]; exact hγπ.ne')
      have hφN : φ ≠ tN := ne_of_angle (by rw [hφπ, aN]; exact hγπ.ne')
      have hUN : tU ≠ tN := by
        obtain ⟨k, hk⟩ := hUt.idx₁
        exact (ne_of_F (GS n ε) hleN (i := k)
          (by rw [hk]; exact GS_gt hf1 hε (by linarith))).symm
      have h3 := three_angles_le D.toDissection (lp n ε x 0 ((j:ℝ) + 1)) hφU hφN hUN
      have h2π := localAngle_le_two_pi D.target (lp n ε x 0 ((j:ℝ) + 1))
      rw [hφπ, aU, aN] at h3
      linarith
    · -- `i = i' + 1`
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hn3 : 3 ≤ n := by omega
      have hN0 := hN
      rw [Nat.cast_add, Nat.cast_one] at hN
      -- (a) the tiles `D(a, j)`, `a ≤ i'`
      have hDa : ∀ a : ℕ, a ≤ i' → DT D n ε x a j := by
        intro a ha
        refine C.D_of (i := a) (j := j) (by omega) (rowsU a j le_rfl (by omega))
          (by
            have h := rowsU (a + 1) j le_rfl (by omega)
            rwa [Nat.cast_add, Nat.cast_one] at h) ?_ ?_ ?_
        · rcases Nat.eq_zero_or_pos j with hj | hj
          · exact Or.inl hj
          · exact Or.inr ⟨hj, rowsD (a + 1) (j - 1) (by omega) (by omega)⟩
        · intro w hw
          refine hA (a + 1) (by omega) (by omega) (a + j + 1) j (by omega) (by omega) (by omega)
            ⟨fun a' b hb hab => rowsU a' b hb (by omega),
              fun a' b hb hab => rowsD a' b hb (by omega)⟩ ?_
          have e1 : (((a + j + 1 : ℕ)) : ℝ) = (a:ℝ) + j + 1 := by push_cast; ring
          rw [e1]
          exact Or.inr ⟨w, hw⟩
        · exact ih a (by omega) j (by omega) (fun a' b hb hab => rowsU a' b hb (by omega))
            (fun a' b hb hab => rowsD a' b hb (by omega)) (fun m' h1 h2 => hA m' h1 (by omega))
      -- (b) the row above
      have hqpos : (0:ℝ) < ((i' + 1 : ℕ) : ℝ) := by positivity
      have hclR : ∃ Q' : Plane, GH n Q' = -((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1)) ∧
          lp n ε x ((i' + 1 : ℕ) : ℝ) ((j:ℝ) + 1) ∈ openSegment ℝ (lp n ε x 0 ((j:ℝ) + 1)) Q' ∧
          ∀ e ∈ D.lineChain (GH n) (-((n:ℝ) ^ 2 * hh n * ((j:ℝ) + 1))),
            ¬ Straddles ((D.tile e.1).edge e.2) Q' (lp n ε x ((i' + 1 : ℕ) : ℝ) ((j:ℝ) + 1))
              (lp n ε x 0 ((j:ℝ) + 1)) := by
        have hQeq : lp n ε x ((i' + 1 : ℕ) : ℝ) ((j:ℝ) + 1)
            + ((1 / 3 : ℝ) / ((i' + 1 : ℕ) : ℝ))
              • (lp n ε x ((i' + 1 : ℕ) : ℝ) ((j:ℝ) + 1) - lp n ε x 0 ((j:ℝ) + 1))
            = lp n ε x (((i' + 1 : ℕ) : ℝ) + 1 / 3) ((j:ℝ) + 1) := by
          rw [lp_ext]
          exact lp_congr (by rw [sub_zero, div_mul_cancel₀ _ hqpos.ne']) (by ring)
        have hmemQ := mem_openSegment_ext (lp n ε x ((i' + 1 : ℕ) : ℝ) ((j:ℝ) + 1))
          (lp n ε x 0 ((j:ℝ) + 1)) (s := (1 / 3 : ℝ) / ((i' + 1 : ℕ) : ℝ)) (by positivity)
        rw [hQeq] at hmemQ
        refine ⟨lp n ε x (((i' + 1 : ℕ) : ℝ) + 1 / 3) ((j:ℝ) + 1), GH_lp _ _ _ _ _,
          by rw [openSegment_symm]; exact hmemQ,
          fun e _ => not_straddles_of_interior D.toDissection (j := tN) ?_ e.1 e.2⟩
        intro y hy
        rw [openSegment_eq_image_lineMap] at hy
        obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
        rw [lineMap_lp]
        have h := N_push S hN0 (δ := (1 - τ) / 3) (by linarith) (by linarith)
        rw [show lp n ε x (((i' + 1 : ℕ) : ℝ) + 1 / 3
              + τ * (((i' + 1 : ℕ) : ℝ) - (((i' + 1 : ℕ) : ℝ) + 1 / 3)))
              ((j:ℝ) + 1 + τ * ((j:ℝ) + 1 - ((j:ℝ) + 1)))
            = lp n ε x (((i' + 1 : ℕ) : ℝ) + (1 - τ) / 3) ((j:ℝ) + 1) from
          lp_congr (by ring) (by ring)]
        exact h
      have hrow := C.row hn3 (j := j) (q := i' + 1) (by omega) hij rowsU rowsD
        (fun a ha => hDa a (by omega)) hclR (fun m' h1 h2 => hA m' h1 (by omega))
      -- (c) the tile across the `a`-edge of `U(i', j+1)` at `p(i'+1, j+1)`
      obtain ⟨t₄, h4⟩ := hrow i' (by omega)
      obtain ⟨t₁, h1⟩ := hDa i' le_rfl
      obtain ⟨t₂, h2⟩ := rowsU (i' + 1) j le_rfl le_rfl
      rw [Nat.cast_add, Nat.cast_one] at h2
      have hFw : ∃ δ : ℝ, 0 < δ ∧ lp n ε x ((i':ℝ) + 1 + δ) ((j:ℝ) + 1) ∈ D.target.carrier :=
        ⟨1 / 3, by norm_num, Erdos634.BaseSelection.tile_subset_target D.toDissection tN
          (interior_subset (N_push S hN (δ := 1 / 3) (by norm_num) le_rfl))⟩
      have hclS : ∃ P' : Plane, GS n ε P' = -lv n ε x ((i':ℝ) + ((j:ℝ) + 1) + 1) ∧
          lp n ε x ((i':ℝ) + 1) ((j:ℝ) + 1) ∈ openSegment ℝ P' (lp n ε x i' ((j:ℝ) + 1 + 1)) ∧
          ∀ e ∈ D.lineChain (GS n ε) (-lv n ε x ((i':ℝ) + ((j:ℝ) + 1) + 1)),
            ¬ Straddles ((D.tile e.1).edge e.2) P' (lp n ε x ((i':ℝ) + 1) ((j:ℝ) + 1))
              (lp n ε x i' ((j:ℝ) + 1 + 1)) := by
        have hleN := hN.all (P := fun p => GS n ε p ≤ -lv n ε x ((i':ℝ) + ((j:ℝ) + 1) + 1))
          (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith)) (GS_le hf1 hε (by linarith))
        obtain ⟨k, m, j₃, hkm, -, -, hk, hm, -⟩ := hN
        exact C.m_clamp_tile hkm (by rw [hk]; exact lp_congr (by ring) (by ring)) hm hleN
      have hb : (i':ℝ) + 2 ≤ n := by
        have h' : i' + 2 ≤ n := by omega
        exact_mod_cast h'
      have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
      rcases C.m_next h4 (by linarith) hFw hclS hb with ⟨t₆, h6⟩ | ⟨t₆, h6⟩ | ⟨w, hw⟩
      · exact C.N_five h1 h2 hN h4 h6
      · -- (d) `N_{i'}(j+1)` is not a tile
        refine ih i' (by omega) (j + 1) (by omega) ?_ ?_ (fun m' h1 h2 => hA m' h1 (by omega)) t₆
          (h6.congr (lp_congr rfl (by rw [Nat.cast_add, Nat.cast_one]))
            (lp_congr rfl (by rw [Nat.cast_add, Nat.cast_one]))
            (lp_congr rfl (by rw [Nat.cast_add, Nat.cast_one])))
        · intro a b hb' hab
          rcases Nat.lt_or_ge b (j + 1) with hlt | hge
          · exact rowsU a b (by omega) (by omega)
          · have hbe : b = j + 1 := by omega
            subst hbe
            have h := hrow a (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro a b hb' hab
          rcases Nat.lt_or_ge b j with hlt | hge
          · exact rowsD a b hlt (by omega)
          · have hbe : b = j := by omega
            subst hbe
            exact hDa a (by omega)
      · -- the tile lays more than `a`: (K3) for the run `(i'+j+2, j+1)`, of size `i'+1`
        refine hA (i' + 1) (by omega) le_rfl (i' + 1 + j + 1) (j + 1) (by omega) (by omega)
          (by omega) ⟨?_, ?_⟩ ?_
        · intro a b hb' hab
          rcases Nat.lt_or_ge b (j + 1) with hlt | hge
          · exact rowsU a b (by omega) (by omega)
          · have hbe : b = j + 1 := by omega
            subst hbe
            have h := hrow a (by omega)
            rw [Nat.cast_add, Nat.cast_one]
            exact h
        · intro a b hb' hab
          rcases Nat.lt_or_ge b j with hlt | hge
          · exact rowsD a b hlt (by omega)
          · have hbe : b = j := by omega
            subst hbe
            exact hDa a (by omega)
        · have e1 : (((i' + 1 + j + 1 : ℕ)) : ℝ) = (i':ℝ) + ((j:ℝ) + 1) + 1 := by
            push_cast; ring
          have e2 : (((j + 1 : ℕ)) : ℝ) = (j:ℝ) + 1 := by push_cast; ring
          rw [e1, e2]
          exact Or.inr ⟨w, hw⟩

/-- **THE CLAIM `K(s, j0)`**, for all pairs `j0 < s < n`: (K1) (in `Ctx`), (K2) and (K3) are contradictory. -/
theorem K_all (C : Ctx D n α β γ L ax ay ε x) : ∀ m : ℕ, 1 ≤ m → Aprop D n ε x m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro hm1 s j0 hj0s hsn hsz hK2 hK3
    obtain ⟨hKU, hKD⟩ := hK2
    have S := C.S
    have hε := C.e2
    have hf1 := S.f1
    have hsj : (j0:ℝ) < s := by exact_mod_cast hj0s
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- size `1`: the chord `[P, p(0,s)]`
      have hs : s = j0 + 1 := by omega
      have hspos : (0:ℝ) < s := by linarith [Nat.cast_nonneg (α := ℝ) j0]
      have hFp : FX n ε (lp n ε x ((s:ℝ) - s) s) = lv n ε x 0 := by
        rw [FX_lp hε]; unfold lv; ring
      have hdir : GS n ε (lp n ε x ((s:ℝ) - s) s - lp n ε x 0 0) < 0 := by
        rw [map_sub, GS_lp hε, GS_lp hε]
        have := lv_lt (n := (n:ℝ)) (ε := ε) (x := x) hf1
          (show (0:ℝ) + 0 < (s:ℝ) - s + s by linarith)
        linarith
      obtain ⟨Q', hfQ', hQ', hQc⟩ := C.K3_clamp hK3 (η := (s:ℝ)) hsj le_rfl (FX n ε) (lv n ε x 0)
        (Q := lp n ε x 0 0) hFp (FX_lp hε 0 0) hdir
      rw [show lp n ε x ((s:ℝ) - s) s = lp n ε x 0 s from lp_congr (by ring) rfl] at hQ' hQc
      refine C.chord (j := s) (by omega) hsn (fun j' hj' => ?_) hfQ'
        (by rw [openSegment_symm]; exact hQ') hQc
      have h := hKU 0 j' (by omega) (by omega)
      rwa [Nat.cast_zero] at h
    · -- size `≥ 2`
      have hn3 : 3 ≤ n := by omega
      -- (2) the tiles `D(i, j0)`
      have hDall : ∀ i : ℕ, i + j0 + 2 ≤ s → DT D n ε x i j0 := by
        intro i hi
        refine C.D_of (i := i) (j := j0) (by omega) (hKU i j0 le_rfl (by omega))
          (by
            have h := hKU (i + 1) j0 le_rfl (by omega)
            rwa [Nat.cast_add, Nat.cast_one] at h) ?_ ?_ ?_
        · rcases Nat.eq_zero_or_pos j0 with hj | hj
          · exact Or.inl hj
          · exact Or.inr ⟨hj, hKD (i + 1) (j0 - 1) (by omega) (by omega)⟩
        · intro w hw
          refine IH (i + 1) (by omega) (by omega) (i + j0 + 1) j0 (by omega) (by omega) (by omega)
            ⟨fun a b hb hab => hKU a b hb (by omega), fun a b hb hab => hKD a b hb (by omega)⟩ ?_
          have e1 : (((i + j0 + 1 : ℕ)) : ℝ) = (i:ℝ) + j0 + 1 := by push_cast; ring
          rw [e1]
          exact Or.inr ⟨w, hw⟩
        · exact C.noN i j0 (by omega) (fun a b hb hab => hKU a b hb (by omega))
            (fun a b hb hab => hKD a b hb (by omega))
            (fun m' h1 h2 => IH m' (by omega) h1)
      -- (3) the row `j0 + 1`
      have hm1' : 1 ≤ m - 1 := by omega
      have hcm : ((m - 1 : ℕ) : ℝ) = (s:ℝ) - ((j0:ℝ) + 1) := by
        have h1 : m - 1 = s - (j0 + 1) := by omega
        rw [h1, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have hFp : GH n (lp n ε x ((s:ℝ) - ((j0:ℝ) + 1)) ((j0:ℝ) + 1))
          = -((n:ℝ) ^ 2 * hh n * ((j0:ℝ) + 1)) := GH_lp _ _ _ _ _
      have hsj1 : (j0:ℝ) + 1 < s := by
        have h' : j0 + 1 < s := by omega
        exact_mod_cast h'
      have hdir : GS n ε (lp n ε x ((s:ℝ) - ((j0:ℝ) + 1)) ((j0:ℝ) + 1) - lp n ε x 0 ((j0:ℝ) + 1))
          < 0 := by
        rw [map_sub, GS_lp hε, GS_lp hε]
        have := lv_lt (n := (n:ℝ)) (ε := ε) (x := x) hf1
          (show (0:ℝ) + ((j0:ℝ) + 1) < (s:ℝ) - ((j0:ℝ) + 1) + ((j0:ℝ) + 1) by linarith)
        linarith
      obtain ⟨Q', hfQ', hQ', hQc⟩ := C.K3_clamp hK3 (η := (j0:ℝ) + 1) (by linarith) hsj1.le (GH n)
        (-((n:ℝ) ^ 2 * hh n * ((j0:ℝ) + 1))) (Q := lp n ε x 0 ((j0:ℝ) + 1)) hFp
        (GH_lp _ _ _ _ _) hdir
      rw [← hcm] at hQ' hQc
      have hrow := C.row hn3 (j := j0) (q := m - 1) hm1' (by omega)
        (fun a b hb hab => hKU a b hb (by omega)) (fun a b hb hab => hKD a b hb (by omega))
        (fun a ha => hDall a (by omega)) ⟨Q', hfQ', by rw [openSegment_symm]; exact hQ', hQc⟩
        (fun m' h1 h2 => IH m' (by omega) h1)
      -- (4) the pair `(s, j0 + 1)`
      refine IH (m - 1) (by omega) hm1' s (j0 + 1) (by omega) hsn (by omega) ⟨?_, ?_⟩ ?_
      · intro a b hb hab
        rcases Nat.lt_or_ge b (j0 + 1) with hlt | hge
        · exact hKU a b (by omega) hab
        · have hbe : b = j0 + 1 := by omega
          subst hbe
          have h := hrow a (by omega)
          rw [Nat.cast_add, Nat.cast_one]
          exact h
      · intro a b hb hab
        rcases Nat.lt_or_ge b j0 with hlt | hge
        · exact hKD a b hlt hab
        · have hbe : b = j0 := by omega
          subst hbe
          exact hDall a (by omega)
      · exact hK3.mono (by push_cast; linarith)

/-- **THE RUN LEMMA `L_k`**, `1 ≤ k < n`.  A run of `k` tiles `U(0,0), …, U(k−1,0)` on the side, with (K1) at its
first end `P` (in `Ctx`) and (K3) at its last end, does not exist. -/
theorem run_dies (C : Ctx D n α β γ L ax ay ε x) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n)
    (hrun : ∀ i : ℕ, i < k → UT D n ε x i 0) (hK3 : K3 D n ε x k 0) : False := by
  refine C.K_all k hk1 k 0 (by omega) hkn (by omega) ⟨?_, ?_⟩ (by rw [Nat.cast_zero]; exact hK3)
  · intro i j hj hij
    have hj0 : j = 0 := by omega
    subst hj0
    rw [Nat.cast_zero]
    exact hrun i (by omega)
  · intro i j hj _
    exact absurd hj (Nat.not_lt_zero j)

end Ctx

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.Ctx.D_of
#print axioms Erdos634.Draft.SideRun.Ctx.noN
#print axioms Erdos634.Draft.SideRun.Ctx.K_all
#print axioms Erdos634.Draft.SideRun.Ctx.run_dies
