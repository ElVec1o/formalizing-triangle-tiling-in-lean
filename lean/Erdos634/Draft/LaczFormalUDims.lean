import Erdos634.Draft.LaczFormalWalkRules
import Erdos634.Draft.SideRunGMain
import Erdos634.Draft.LaczFormalChainDims

/-!
# Theorem U for a real dissection of `T_M(e,f)`: no tiling for `2Me ≤ f+1`

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program; Band Lemma, Prop. B1, rule C0, Theorem U),
Beeson–Roșu (Lemmas 28–37, tile and `T_M`), Beeson, Laczkovich, Paliy, Zhang.  UNAUDITED.
Axiom-clean; no `sorry`.  Not imported by `AllLacz` (its closure contains `SideRunGMain`, `AllThreshold`).
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.W2E1 Erdos634.Draft.SideRunG
  Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1

variable {N : ℕ}

theorem count_map_eq (h : (Fin N × Plane × Plane) → Tok) (L : List (Fin N × Plane × Plane)) (a : Tok) :
    (L.map h).count a = L.countP (fun x => decide (h x = a)) := by
  induction L with
  | nil => simp
  | cons x r ih => simp [List.count_cons, List.countP_cons, ih]

theorem count_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι] {L : List (Fin N × Plane × Plane)}
    (hnd : L.Nodup) (pred : (Fin N × Plane × Plane) → Bool) (g : ι → (Fin N × Plane × Plane))
    (hg : ∀ j, g j ∈ L ∧ pred (g j) = true) (hinj : Function.Injective g) :
    Fintype.card ι ≤ L.countP pred := by
  classical
  have h1 : (Finset.univ.image g).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have h2 : Finset.univ.image g ⊆ (L.filter pred).toFinset := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    simp [hg j]
  have h3 := Finset.card_le_card h2
  have h4 : (L.filter pred).toFinset.card = (L.filter pred).length :=
    List.toFinset_card_of_nodup (hnd.filter _)
  rw [← h1, List.countP_eq_length_filter]
  omega

theorem laid_entry {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (i : Fin N) (ka kb jj : Fin 3) (hkab : ka ≠ kb) (hkaj : ka ≠ jj) (hkbj : kb ≠ jj) {s1 s2 : ℝ}
    (h01 : 0 ≤ s1) (h12 : s1 < s2) (h21 : s2 ≤ 1)
    (hka : (D.tile i).pts ka = D.target.pts p + s1 • (D.target.pts q - D.target.pts p))
    (hkb : (D.tile i).pts kb = D.target.pts p + s2 • (D.target.pts q - D.target.pts p))
    (hlen : dist (D.target.pts p + s1 • (D.target.pts q - D.target.pts p))
      (D.target.pts p + s2 • (D.target.pts q - D.target.pts p)) = sideOpp D.model 2) :
    ∃ x ∈ L, x.1 = i ∧ x.2.1 = D.target.pts p + s1 • (D.target.pts q - D.target.pts p) ∧
      x.2.2 = D.target.pts p + s2 • (D.target.pts q - D.target.pts p) ∧
      ((dist ((D.tile i).pts kb) ((D.tile i).pts jj) = sideOpp D.model 0 → elemTok D α β x = Tok.cAB) ∧
       (dist ((D.tile i).pts kb) ((D.tile i).pts jj) = sideOpp D.model 1 → elemTok D α β x = Tok.cBA)) := by
  obtain ⟨x, hx, h1, h2, h3⟩ := entry_of_laid S.hpq S.hpr S.hqr hori hL i ka kb hkab.symm h01 h12 h21 hka hkb
  refine ⟨x, hx, h1, h2, h3, ?_⟩
  have hx' : x = (i, D.target.pts p + s1 • (D.target.pts q - D.target.pts p),
      D.target.pts p + s2 • (D.target.pts q - D.target.pts p)) := by
    ext <;> simp [h1, h2, h3]
  rw [hx']
  exact laid_tok S i ka kb jj hkab hkaj hkbj hka.symm.symm hkb.symm.symm hlen

theorem lineMap_eq (P Q : Plane) (c : ℝ) : AffineMap.lineMap P Q c = P + c • (Q - P) := by
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

theorem dist_two_param (P Q : Plane) {s1 s2 : ℝ} (h : s1 ≤ s2) :
    dist (P + s1 • (Q - P)) (P + s2 • (Q - P)) = (s2 - s1) * dist P Q := by
  rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_of_nonpos (by linarith),
    dist_comm P Q, dist_eq_norm]
  ring

/-- The run of the side theorem gives `f` entries of one of the two types. -/
theorem run_count {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {L : List (Fin N × Plane × Plane)}
    (hL : WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) L)
    (hnd : L.Nodup)
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (hend : x₀ + (f : ℝ) * (f : ℝ) ^ 2 ≤ dist (D.target.pts p) (D.target.pts q))
    {t : ℕ → Fin N}
    (hrun : (∀ j, j < f → LaysBaseOn D (e : ℝ) (f : ℝ) (D.target.pts p) (D.target.pts q) (t j) Ty.C1
          (x₀ + j * (f : ℝ) ^ 2)) ∨
       (∀ j, j < f → LaysBaseOn D (e : ℝ) (f : ℝ) (D.target.pts p) (D.target.pts q) (t j) Ty.C2
          (x₀ + j * (f : ℝ) ^ 2))) :
    RunCount f (L.map (elemTok D α β)) := by
  classical
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  have hne : P ≠ Q := by
    intro h
    have : cross (Q - P) (D.target.pts r - P) = 0 := by rw [← h]; simp [cross]
    linarith
  have hL0 : 0 < dist P Q := dist_pos.mpr hne
  have hf2 : (0:ℝ) < (f:ℝ) ^ 2 := by
    have : 0 < f := by have := S.hef; have := S.he; omega
    positivity
  have hsc : sideOpp D.model 2 = (f:ℝ) ^ 2 := by rw [S.hsc]; simp [tc]
  have hsa : sideOpp D.model 0 = (e:ℝ) * f := by rw [S.hsa]; simp [ta]
  have hsb : sideOpp D.model 1 = (f:ℝ) ^ 2 - (e:ℝ) ^ 2 := by rw [S.hsb, tb_real e f S.hef]
  have hlenC : (Ty.C1).lenG (e:ℝ) f = (f:ℝ) ^ 2 := rfl
  have hlenC2 : (Ty.C2).lenG (e:ℝ) f = (f:ℝ) ^ 2 := rfl
  have key : ∀ (T : Ty), (T.lenG (e:ℝ) f = (f:ℝ) ^ 2) →
      (∀ j, j < f → LaysBaseOn D (e : ℝ) (f : ℝ) P Q (t j) T (x₀ + j * (f : ℝ) ^ 2)) →
      ∀ j, j < f → ∃ x ∈ L, x.1 = t j ∧ x.2.1 = P + ((x₀ + j * (f:ℝ) ^ 2) / dist P Q) • (Q - P) ∧
        ((T.sRG (e:ℝ) f = (e:ℝ) * f → elemTok D α β x = Tok.cAB) ∧
         (T.sRG (e:ℝ) f = (f:ℝ) ^ 2 - (e:ℝ) ^ 2 → elemTok D α β x = Tok.cBA)) := by
    intro T hT hall j hj
    obtain ⟨ka, kb, jj, hkab, hkaj, hkbj, hpa, hpb, hsL, hsR⟩ := hall j hj
    rw [lineMap_eq] at hpa hpb
    rw [hT] at hpb
    have hjf : (j:ℝ) + 1 ≤ f := by exact_mod_cast hj
    have hxj : 0 ≤ x₀ + j * (f:ℝ) ^ 2 := by positivity
    have h01 : 0 ≤ (x₀ + j * (f:ℝ) ^ 2) / dist P Q := div_nonneg hxj hL0.le
    have h12 : (x₀ + j * (f:ℝ) ^ 2) / dist P Q < (x₀ + j * (f:ℝ) ^ 2 + (f:ℝ) ^ 2) / dist P Q :=
      div_lt_div_of_pos_right (by linarith) hL0
    have h21 : (x₀ + j * (f:ℝ) ^ 2 + (f:ℝ) ^ 2) / dist P Q ≤ 1 := by
      rw [div_le_one hL0]
      nlinarith
    have hlen : dist (P + ((x₀ + j * (f:ℝ) ^ 2) / dist P Q) • (Q - P))
        (P + ((x₀ + j * (f:ℝ) ^ 2 + (f:ℝ) ^ 2) / dist P Q) • (Q - P)) = sideOpp D.model 2 := by
      rw [dist_two_param P Q h12.le, hsc]
      field_simp
      ring
    obtain ⟨x, hx, h1, h2, h3, h4⟩ := laid_entry S hori hL (t j) ka kb jj hkab hkaj hkbj h01 h12 h21
      hpa hpb hlen
    refine ⟨x, hx, h1, h2, ?_, ?_⟩
    · intro h
      apply h4.1
      rw [dist_comm, hsa, ← h]; exact hsR
    · intro h
      apply h4.2
      rw [dist_comm, hsb, ← h]; exact hsR
  have inj : ∀ (g : Fin f → (Fin N × Plane × Plane)),
      (∀ j : Fin f, (g j).2.1 = P + ((x₀ + (j:ℕ) * (f:ℝ) ^ 2) / dist P Q) • (Q - P)) →
      Function.Injective g := by
    intro g hg j j' hjj
    have h1 := hg j
    have h2 := hg j'
    rw [hjj] at h1
    have h3 := h1.symm.trans h2
    have hw : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h4 := smul_injective_of_ne hw (add_left_cancel h3)
    have h5 : ((j':ℕ):ℝ) * (f:ℝ) ^ 2 = ((j:ℕ):ℝ) * (f:ℝ) ^ 2 := by
      have := (div_left_inj' hL0.ne').mp h4
      linarith
    have h6 : ((j':ℕ):ℝ) = ((j:ℕ):ℝ) := mul_right_cancel₀ hf2.ne' h5
    exact Fin.ext (by exact_mod_cast h6.symm)
  have runcnt : ∀ tk : Tok, (∀ j, j < f → ∃ x ∈ L, x.2.1 = P + ((x₀ + j * (f:ℝ) ^ 2) / dist P Q) • (Q - P) ∧
      elemTok D α β x = tk) → f ≤ (L.map (elemTok D α β)).count tk := by
    intro tk hall
    have hall' : ∀ j : Fin f, ∃ x ∈ L, x.2.1 = P + ((x₀ + (j:ℕ) * (f:ℝ) ^ 2) / dist P Q) • (Q - P) ∧
        elemTok D α β x = tk := fun j => hall j j.2
    choose g hgL hg2 hg3 using hall'
    have := count_of_entries hnd (fun x => decide (elemTok D α β x = tk)) g
      (fun j => ⟨hgL j, by simpa using hg3 j⟩) (inj g hg2)
    rw [count_map_eq]
    simpa using this
  rcases hrun with hr | hr
  · left
    refine runcnt Tok.cAB (fun j hj => ?_)
    obtain ⟨x, hx, -, h2, h3⟩ := key Ty.C1 hlenC hr j hj
    exact ⟨x, hx, h2, h3.1 rfl⟩
  · right
    refine runcnt Tok.cBA (fun j hj => ?_)
    obtain ⟨x, hx, -, h2, h3⟩ := key Ty.C2 hlenC2 hr j hj
    exact ⟨x, hx, h2, h3.2 rfl⟩

#print axioms run_count

theorem exists_perm_pqr (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ τ : Equiv.Perm (Fin 3), τ 0 = p ∧ τ 1 = q ∧ τ 2 = r := by
  revert hpq hpr hqr; revert p q r; decide

/-- **Theorem U (oriented form).** No `CongruentDissection` of `T_M(e,f)` by `(ef, f²−e², f²)` with `e ≥ 2` and
`2Me ≤ f + 1`, the target positively oriented on `p → q`.  Uses only: Lean `thm_siderunall_T_pinned`,
the Band Lemma `band_lemma` (proved here), `band_C0_full`, `band_C0m_full`. -/
theorem no_tiling_U_oriented (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hd : 2 * M * e ≤ f + 1) : False := by
  classical
  have S := BandSetup.of_dims D e f M (by omega) hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR
  have hori' : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) := by
    rw [crs_toV2]; exact hori
  obtain ⟨L, hL, hpar, hnd, hstep⟩ := base_walk S hori'
  set α := modelAlpha (e : ℝ) f
  set β := modelBeta (e : ℝ) f
  set γ := 2 * α + β
  have hbt : ∀ x ∈ L, ∃ Z, BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
      (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2 Z := by
    intro x hx
    obtain ⟨kk, fi, g, -, -, -, -, -, -, hb⟩ := hstep x hx
    exact ⟨_, hb⟩
  have htot := walk_total (M := M) (r := r) hL hbt hbase
  -- the run
  obtain ⟨τ, hτ0, hτ1, hτ2⟩ := exists_perm_pqr p q r hpq hpr hqr
  have heR : (1:ℝ) ≤ e := by exact_mod_cast (by omega : 1 ≤ e)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hbaseR : dist (D.target.pts p) (D.target.pts q) =
      (M:ℝ) * ((e:ℝ) * (3 * (f:ℝ) ^ 2 - (e:ℝ) ^ 2)) := by
    rw [hbase]
    have : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]; ring
  have hlegLR : dist (D.target.pts p) (D.target.pts r) = (M:ℝ) * (f:ℝ) ^ 3 := by rw [hlegL]; push_cast; ring
  have hlegRR : dist (D.target.pts q) (D.target.pts r) = (M:ℝ) * (f:ℝ) ^ 3 := by rw [hlegR]; push_cast; ring
  have hMod : HasSides D.model ((e:ℝ) * f) ((f:ℝ) ^ 2 - (e:ℝ) ^ 2) ((f:ℝ) ^ 2) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
    · show sideOpp D.model 0 = _
      rw [hsa]; simp [ta]
    · show sideOpp D.model 1 = _
      rw [hsb, tb_real e f hef]
    · show sideOpp D.model 2 = _
      rw [hsc]; simp [tc]
  obtain ⟨x₀, t, h0, hend, hrun, -⟩ := thm_siderunall_T_pinned e f (by omega) hef hcop (s := (M:ℝ)) hMR D
    τ (by rw [hτ1, hτ2]; exact hlegRR) (by rw [hτ2, hτ0, dist_comm]; exact hlegLR)
    (by rw [hτ0, hτ1]; exact hbaseR) hMod
  rw [hτ0, hτ1] at hrun
  rw [← hbaseR] at hend
  have hrc := run_count S hori hL hnd h0 hend hrun
  have hC : f ≤ countC (L.map (elemTok D α β)) := by
    have := count_add_le_countC (L.map (elemTok D α β))
    rcases hrc with h | h <;> omega
  -- B1
  by_cases hlt : 2 * M * e < f
  · exact b1_thin e f M (by omega) hef hcop hM hlt _ htot hC
  have hlo : f ≤ 2 * M * e := by omega
  have hhi : 2 * M * e < f + e := by omega
  obtain ⟨hno, hcount⟩ := b1_of_total e f M (by omega) hef hcop hM hlo hhi _ htot hC
  have hlen : 2 ≤ (L.map (elemTok D α β)).length := by
    have := countC_le_length (L.map (elemTok D α β))
    have h2 : 2 ≤ f := by omega
    have : 2 * 2 ≤ 2 * M * e := by nlinarith
    omega
  -- the corner tokens
  obtain ⟨x, L1, hxL⟩ : ∃ x L1, L = x :: L1 := by
    rcases L with _ | ⟨x, L1⟩
    · simp at hlen
    · exact ⟨x, L1, rfl⟩
  obtain ⟨L2, y, hyL⟩ : ∃ L2 y, L = L2 ++ [y] := by
    rcases List.eq_nil_or_concat L with h | ⟨L2, y, h⟩
    · rw [h] at hxL; simp at hxL
    · exact ⟨L2, y, by rw [h, List.concat_eq_append]⟩
  have hx0 : x.2.1 = D.target.pts p := walk_first hL x L1 hxL
  have hy1 : y.2.2 = D.target.pts q := walk_last hL L2 y hyL
  have hfirst : ∃ t, (L.map (elemTok D α β)).head? = some t ∧ okFirst t :=
    ⟨elemTok D α β x, by rw [hxL]; rfl, (okFirst_iff _).2 (first_left_B S hx0 (hstep x (by rw [hxL]; simp)))⟩
  have hlast : ∃ t, (L.map (elemTok D α β)).getLast? = some t ∧ okLast t :=
    ⟨elemTok D α β y, by rw [hyL]; simp, (okLast_iff _).2 (last_right_B S hy1 (hstep y (by rw [hyL]; simp)))⟩
  rcases U_core' f (2 * M * e) _ hno hfirst hlast hrc hcount hlen (by omega) with h | h
  · exact walk_noC0 S hori' hL hpar hstep h
  · exact walk_noC0m S hori' hL hpar hstep h


theorem cross_sq (P Q R : Plane) :
    (cross (Q - P) (R - P)) ^ 2 = dist P Q ^ 2 * dist P R ^ 2 -
      ((dist P Q ^ 2 + dist P R ^ 2 - dist Q R ^ 2) / 2) ^ 2 := by
  have h1 := Erdos634.Geometry.norm_sq_coords (Q - P)
  have h2 := Erdos634.Geometry.norm_sq_coords (R - P)
  have h3 := Erdos634.Geometry.norm_sq_coords (R - Q)
  rw [dist_comm P Q, dist_comm P R, dist_comm Q R, dist_eq_norm, dist_eq_norm, dist_eq_norm, h1, h2, h3]
  simp only [cross, PiLp.sub_apply]
  ring

theorem dims_cross_ne (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f) (hM : 1 ≤ M)
    {p q r : Fin 3}
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ)) :
    cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) ≠ 0 := by
  intro h0
  have hsq := cross_sq (D.target.pts p) (D.target.pts q) (D.target.pts r)
  rw [h0, hbase, hlegL, hlegR] at hsq
  have heR : (2:ℝ) ≤ e := by exact_mod_cast he
  have hefR : (e:ℝ) < f := by exact_mod_cast hef
  have hMR : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hlt := baseLen_lt (e := (e:ℝ)) (f := (f:ℝ)) (by linarith) hefR
  unfold baseLen Nq at hlt
  have hb : ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) = (M:ℝ) * ((e:ℝ) * (3 * (f:ℝ) ^ 2 - (e:ℝ) ^ 2)) := by
    have : e ^ 2 ≤ 3 * f ^ 2 := by nlinarith
    push_cast [Nat.cast_sub this]; ring
  have hL : ((M * f ^ 3 : ℕ) : ℝ) = (M:ℝ) * (f:ℝ) ^ 3 := by push_cast; ring
  rw [hb, hL] at hsq
  have hf0 : (0:ℝ) < f := by linarith
  have hN : 0 < 3 * (f:ℝ) ^ 2 - (e:ℝ) ^ 2 := by nlinarith
  have hpos : 0 < (e:ℝ) * (3 * (f:ℝ) ^ 2 - (e:ℝ) ^ 2) := mul_pos (by linarith) hN
  have hM0 : 0 < (M:ℝ) := by linarith
  set A := (M:ℝ) * ((e:ℝ) * (3 * (f:ℝ) ^ 2 - (e:ℝ) ^ 2)) with hA
  set Lg := (M:ℝ) * (f:ℝ) ^ 3 with hLg
  have hApos : 0 < A := mul_pos hM0 hpos
  have hAL : A < 2 * Lg := by rw [hA, hLg]; nlinarith
  have h4 : A ^ 2 * ((2 * Lg) ^ 2 - A ^ 2) = 0 := by linear_combination (-4 : ℝ) * hsq
  have h5 : (2 * Lg) ^ 2 - A ^ 2 = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h (by positivity)
    · exact h
  nlinarith

/-- **Theorem U.** No `CongruentDissection` of the isosceles triangle `T_M(e,f)` (base `[p,q]` of length
`M e (3f² − e²)`, legs `M f³`) by copies of `(ef, f²−e², f²)`, for `e ≥ 2`, `M ≥ 1`, `2Me ≤ f + 1`
(coprime `e < f`).  Reflections allowed, any number of tiles. -/
theorem no_tiling_U (D : CongruentDissection N) (e f M : ℕ) (he : 2 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hM : 1 ≤ M)
    (hsa : sideOpp D.model 0 = (ta e f : ℝ)) (hsb : sideOpp D.model 1 = (tb e f : ℝ))
    (hsc : sideOpp D.model 2 = (tc e f : ℝ))
    {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hbase : dist (D.target.pts p) (D.target.pts q) = ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ))
    (hlegL : dist (D.target.pts p) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hlegR : dist (D.target.pts q) (D.target.pts r) = ((M * f ^ 3 : ℕ) : ℝ))
    (hd : 2 * M * e ≤ f + 1) : False := by
  have hne0 := dims_cross_ne D e f M (by omega) hef hM hbase hlegL hlegR
  rcases lt_or_gt_of_ne hne0 with hneg | hpos
  · refine no_tiling_U_oriented D e f M he hef hcop hM hsa hsb hsc (p := q) (q := p) (r := r)
      hpq.symm hqr hpr (by rw [dist_comm]; exact hbase) hlegR hlegL ?_ hd
    have : cross (D.target.pts p - D.target.pts q) (D.target.pts r - D.target.pts q) =
        - cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; linarith
  · exact no_tiling_U_oriented D e f M he hef hcop hM hsa hsb hsc hpq hpr hqr hbase hlegL hlegR hpos hd

#print axioms no_tiling_U

end Erdos634.LaczJunction.Walk
