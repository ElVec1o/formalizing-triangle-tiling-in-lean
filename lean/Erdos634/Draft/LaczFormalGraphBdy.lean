-- Draft/LaczFormalGraphBdy.lean -- D5 (part 6): boundary vertices.  `Gamma` edge bridges for arbitrary sector families (not only `ExtFan`), the angle equation at a vertex,
-- and Lemma 8.1 (iii): a vertex in the relative interior of a side of the target is `SideNormal` (three corner tiles, types pairwise distinct, no differing first sides on the
-- inner rays) as soon as no edge of `Gamma_a u Gamma_k` starts there.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 8.1 (iii)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalGraphBal
import Erdos634.Draft.LaczFormalGraphSideStep

open scoped Classical
open Erdos634.Geometry Erdos634.KConj

namespace Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem gk_of_ray' (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} (p q : AtV D.toDissection H → V2)
    (x y : AtV D.toDissection H) (hxy : Par (p y) (q x)) (hne : x ≠ y)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hpx : p x = toV2 ((D.tile x.1).pts (armP kx flx) - H)) (hqx : q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H))
    (hpy : p y = toV2 ((D.tile y.1).pts (armP ky fly) - H)) (hqy : q y = toV2 ((D.tile y.1).pts (armQ ky fly) - H))
    (t2x : idx x.1 kx = 2) (t1x : idx x.1 (armQ kx flx) = 1) (t2y : idx y.1 ky = 2) (t1y : idx y.1 (armP ky fly) = 1) :
    ∃ Z, GkEdge D.toDissection idx H Z := by
  have hxA : idx x.1 (armP kx flx) = 0 :=
    perm_third (idx x.1) kx (armQ kx flx) (armP kx flx) (armQ_ne kx flx).symm (armP_ne kx flx).symm (armPQ_ne kx flx).symm t2x t1x
  have hyA : idx y.1 (armQ ky fly) = 0 :=
    perm_third (idx y.1) ky (armP ky fly) (armQ ky fly) (armP_ne ky fly).symm (armQ_ne ky fly).symm (armPQ_ne ky fly) t2y t1y
  have hnx : nsq (q x) = slen D 0 ^ 2 := (nsq_q_iff D idx hidx hab hac flx hkx hqx).mpr hxA
  have hny : nsq (p y) = slen D 0 ^ 2 := (nsq_p_iff D idx hidx hab hac fly hky hpy).mpr hyA
  have heq : p y = q x := par_eq_of_nsq hxy (by rw [hnx, hny])
  have hPP : (D.tile x.1).pts (armQ kx flx) = (D.tile y.1).pts (armP ky fly) := by
    apply pt_eq_of_toV2 (H := H)
    rw [← hqx, ← hpy, heq]
  refine ⟨(D.tile x.1).pts (armQ kx flx), x.1, y.1, kx, armQ kx flx, ky, armP ky fly, fun h => hne (Subtype.ext h), hkx, rfl, hky, hPP.symm,
    t2x, t1x, t2y, t1y⟩


theorem ga_edge_of_ray' (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {H : Plane} (p q : AtV D.toDissection H → V2)
    (hok : ∀ s, SecOK (p s) (q s)) (hspec : ∀ s, SectorSpec (D.tile s.1) H (p s) (q s))
    (x y : AtV D.toDissection H) (hcx : 0 < crs (p x) (q x)) (hcy : 0 < crs (p y) (q y))
    (hxy : Par (p y) (q x)) (hnb : NoBack D.toDissection (q x) H)
    (hxor : (nsq (q x) = slen D 0 ^ 2 ∧ nsq (p y) ≠ slen D 0 ^ 2) ∨
            (nsq (q x) ≠ slen D 0 ^ 2 ∧ nsq (p y) = slen D 0 ^ 2)) :
    ∃ H', GaEdge D.toDissection (slen D 0) H H' := by
  classical
  have hd : q x ≠ 0 := (hok x).ne_q
  have hcornx : ∃ k, (D.tile x.1).pts k = H := by
    rcases hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcx; unfold crs at hcx; try simp only at hcx; nlinarith
  have horny : ∃ k, (D.tile y.1).pts k = H := by
    rcases hspec y with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcy; unfold crs at hcy; try simp only at hcy; nlinarith
  obtain ⟨kx, flx, hkx, hpx, hqx⟩ := spec_corner_data (hspec x) hcornx
  obtain ⟨ky, fly, hky, hpy, hqy⟩ := spec_corner_data (hspec y) horny
  have hstepR := triStep_of_end (T := D.tile x.1) (d := q x) kx flx hkx hpx hqx hcx (par_refl hd)
  have hstepL := triStep_of_start (T := D.tile y.1) (d := q x) ky fly hky hpy hqy hcy hxy
  have hX : ∃ j k, (D.tile j).pts k = H := ⟨y.1, ky, hky⟩
  have hdL : dist H ((D.tile y.1).pts (armP ky fly)) ^ 2 = nsq (p y) := by
    rw [hpy, nsq_toV2_sub, dist_comm]
  have hdR : dist ((D.tile x.1).pts (armQ kx flx)) H ^ 2 = nsq (q x) := by
    rw [hqx, nsq_toV2_sub]
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the right first side is `a`: right version
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H = slen D 0 := by
      have := hdR.trans h1
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hla : dist H ((D.tile y.1).pts (armP ky fly)) ≠ slen D 0 := by
      intro h; apply h2; rw [← hdL, h]
    exact ga_edge_of_local' D idx hidx hnc hd hX hnb hstepL hla hstepR hra
  · have hla : dist H ((D.tile y.1).pts (armP ky fly)) = slen D 0 := by
      have := hdL.trans h2
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H ≠ slen D 0 := by
      intro h; apply h1; rw [← hdR, h]
    exact ga_edge_of_local D idx hidx hnc hd hX hnb hstepL hla hstepR hra


section NB
variable {D : Dissection N} {V : Plane}

theorem noBack_of_none' (p q : AtV D V → V2) (hok : ∀ s, SecOK (p s) (q s)) (hloc : ∀ s, LocalCone (D.tile s.1) V (p s) (q s))
    (hspec : ∀ s, SectorSpec (D.tile s.1) V (p s) (q s)) {d : V2}
    (hnone : ∀ s : AtV D V, ¬ Par (p s) (neg2 d) ∧ ¬ Par (q s) (neg2 d)) : NoBack D d V := by
  classical
  constructor
  · intro i A B σ hS h0 h1 hV
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
    by_cases hσ : σ = 1
    · -- V = B, the head: the tile has an arm along -d at V
      subst hσ
      have hVB : V = B := by rw [hV]; simp
      have hmem : V ∈ (D.tile i).carrier := by rw [hVB, ← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
      set s : AtV D V := ⟨i, hmem⟩
      obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (hspec s) ⟨f, by rw [hf, hVB]⟩
      have hS' : TriStep (D.tile i) d A V := by rw [hVB]; exact hS
      have := triStep_end hS' kk' fl' hk' hp hq (hok s)
      exact (hnone s).2 this
    · have hσ1 : σ < 1 := lt_of_le_of_ne h1 hσ
      obtain ⟨hmemV, hnv, hline⟩ := step_interior_pt hS h0 hσ1
      rw [← hV] at hmemV hnv hline
      set s : AtV D V := ⟨i, hmemV⟩
      obtain ⟨hpar', hq⟩ := straight_dir s (hok s) (hloc s) (hspec s) hnv hS hline
      refine (hnone s).2 ?_
      rw [hq]
      have := par_neg hpar'
      exact this
  · intro i A B σ hS h0 h1 hV
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
    by_cases hσ : σ = 1
    · -- V = A, the tail: the tile has an arm along -d at V
      subst hσ
      have hVA : V = A := by rw [hV]; simp
      have hmem : V ∈ (D.tile i).carrier := by rw [hVA, ← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
      set s : AtV D V := ⟨i, hmem⟩
      obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (hspec s) ⟨kk, by rw [hk, hVA]⟩
      have hS' : TriStep (D.tile i) (neg2 d) V B := by rw [hVA]; exact hS
      have := triStep_start hS' kk' fl' hk' hp hq (hok s)
      exact (hnone s).1 this
    · have hσ1 : σ < 1 := lt_of_le_of_ne h1 hσ
      -- V = B + σ • (A - B) = A + (1 - σ) • (B - A)
      have hV' : V = A + (1 - σ) • (B - A) := by rw [hV]; ext i; simp; ring
      obtain ⟨hmemV, hnv, hline⟩ := step_interior_pt hS (by linarith : 0 < 1 - σ) (by linarith : 1 - σ < 1)
      rw [← hV'] at hmemV hnv hline
      set s : AtV D V := ⟨i, hmemV⟩
      obtain ⟨hpar', hq⟩ := straight_dir s (hok s) (hloc s) (hspec s) hnv hS hline
      exact (hnone s).1 hpar'


end NB

theorem tile_localAngle_decomp (D : CongruentDissection N) {V : Plane} (hv : ∃ i k, (D.tile i).pts k = V) (i : Fin N) :
    (D.tile i).localAngle V = vc (D.tile i) V + (if i ∈ Strn D.toDissection V then Real.pi else 0) := by
  classical
  by_cases hk : ∃ k, (D.tile i).pts k = V
  · obtain ⟨k, hk⟩ := hk
    have hnS : i ∉ Strn D.toDissection V := by
      simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_not]
      intro _; exact ⟨k, hk⟩
    have e := vc_of_vertex (D.tile i) k
    rw [hk] at e
    rw [if_neg hnS, ← e]; ring
  · push Not at hk
    have hvc : vc (D.tile i) V = 0 := vc_of_nonvertex _ _ (fun v h => hk v h.symm)
    by_cases hm : V ∈ (D.tile i).carrier
    · have hS : i ∈ Strn D.toDissection V := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hm, hk⟩
      have hfr : V ∈ frontier (D.tile i).carrier := by
        refine ⟨?_, not_interior_of_vertex D.toDissection hv i⟩
        rw [(D.tile i).isCompact.isClosed.closure_eq]; exact hm
      have := Tri.localAngle_frontier (D.tile i) hfr (fun ⟨k, h⟩ => hk k h)
      rw [if_pos hS, hvc, this]; ring
    · have hnS : i ∉ Strn D.toDissection V := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; exact absurd h hm
      rw [if_neg hnS, hvc, Tri.localAngle_eq_zero_of_not_mem _ hm]; ring

/-- **The angle equation at a vertex**: corner angles plus `π` per tile having the vertex inside a side equal the local angle of the target. -/
theorem vertex_angle_eq (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {V : Plane} (hv : ∃ i k, (D.tile i).pts k = V) :
    ∑ l, (cnt D idx V l : ℝ) * D.model.angleAt l + Real.pi * (Strn D.toDissection V).card = D.target.localAngle V := by
  classical
  rw [← D.toDissection.sum_localAngle_eq V, sum_vc_eq D idx hidxA V]
  have : ∀ i, (D.tile i).localAngle V = vc (D.tile i) V + (if i ∈ Strn D.toDissection V then Real.pi else 0) := tile_localAngle_decomp D hv
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Counts at a vertex on the open side of the target**: no tile has the vertex inside a side, the three corners are `(0,0,3)` or `(1,1,1)`, and exactly three tiles meet there. -/
theorem side_counts (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (harith : HalfPlaneArith D) {V : Plane} {m : Fin 3}
    (h0 : D.target.basis.coord m V = 0) (hpos : ∀ j, j ≠ m → 0 < D.target.basis.coord j V) (hv : ∃ i k, (D.tile i).pts k = V)
    (hreg : cnt D idx V 0 = cnt D idx V 1) :
    (Strn D.toDissection V).card = 0 ∧
    ((cnt D idx V 0 = 0 ∧ cnt D idx V 1 = 0 ∧ cnt D idx V 2 = 3) ∨ (cnt D idx V 0 = 1 ∧ cnt D idx V 1 = 1 ∧ cnt D idx V 2 = 1)) ∧
    Fintype.card (AtV D.toDissection V) = 3 := by
  classical
  have hang := vertex_angle_eq D idx hidxA hv
  rw [localAngle_of_edge_coords D.target m V h0 hpos] at hang
  have hcorn : 0 < (Corn D.toDissection V).card := by
    obtain ⟨i, k, hk⟩ := hv
    exact Finset.card_pos.mpr ⟨i, by simp [Corn]; exact ⟨k, hk⟩⟩
  rw [card_corn D idx V, Fin.sum_univ_three] at hcorn
  have hA0 := model_angle_pos D 0
  have hA1 := model_angle_pos D 1
  have hA2 := model_angle_pos D 2
  rw [Fin.sum_univ_three] at hang
  have hSpos : 0 < (cnt D idx V 0 : ℝ) * D.model.angleAt 0 + cnt D idx V 1 * D.model.angleAt 1 + cnt D idx V 2 * D.model.angleAt 2 := by
    by_cases h0' : 0 < cnt D idx V 0
    · have : (0:ℝ) < cnt D idx V 0 := by exact_mod_cast h0'
      have := mul_pos this hA0
      have := mul_nonneg (Nat.cast_nonneg (cnt D idx V 1) : (0:ℝ) ≤ _) hA1.le
      have := mul_nonneg (Nat.cast_nonneg (cnt D idx V 2) : (0:ℝ) ≤ _) hA2.le
      linarith
    · by_cases h1' : 0 < cnt D idx V 1
      · have : (0:ℝ) < cnt D idx V 1 := by exact_mod_cast h1'
        have := mul_pos this hA1
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx V 0) : (0:ℝ) ≤ _) hA0.le
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx V 2) : (0:ℝ) ≤ _) hA2.le
        linarith
      · have h2' : 0 < cnt D idx V 2 := by omega
        have : (0:ℝ) < cnt D idx V 2 := by exact_mod_cast h2'
        have := mul_pos this hA2
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx V 0) : (0:ℝ) ≤ _) hA0.le
        have := mul_nonneg (Nat.cast_nonneg (cnt D idx V 1) : (0:ℝ) ≤ _) hA1.le
        linarith
  have hStr : (Strn D.toDissection V).card = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ (Strn D.toDissection V).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hp := Real.pi_pos
    nlinarith
  rw [hStr] at hang
  have hS : (cnt D idx V 0 : ℝ) * D.model.angleAt 0 + cnt D idx V 1 * D.model.angleAt 1 + cnt D idx V 2 * D.model.angleAt 2 = Real.pi := by
    simpa using hang
  have hcls := harith _ _ _ hS hreg
  refine ⟨hStr, ?_, ?_⟩
  · rcases hcls with ⟨h0', h2'⟩ | ⟨h0', h2'⟩
    · left; exact ⟨h0', by omega, h2'⟩
    · right; exact ⟨h0', by omega, h2'⟩
  · rw [card_atV, card_corn D idx V, hStr, Fin.sum_univ_three]
    rcases hcls with ⟨h0', h2'⟩ | ⟨h0', h2'⟩ <;> omega

theorem fin3_01 (a b : Fin 3) (hab : a ≠ b) (ha : a ≠ 2) (hb : b ≠ 2) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  revert a b; decide

theorem arms_01 (σ : Equiv.Perm (Fin 3)) (kk : Fin 3) (fl : Bool) (h : σ kk = 2) :
    (σ (armP kk fl) = 0 ∧ σ (armQ kk fl) = 1) ∨ (σ (armP kk fl) = 1 ∧ σ (armQ kk fl) = 0) := by
  refine fin3_01 _ _ ?_ ?_ ?_
  · intro e; exact armPQ_ne kk fl (σ.injective e)
  · intro e; exact armP_ne kk fl (σ.injective (e.trans h.symm))
  · intro e; exact armQ_ne kk fl (σ.injective (e.trans h.symm))

theorem cnt_two (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane} (l : Fin 3) {t1 t2 : Fin N} {k1 k2 : Fin 3}
    (hne : t1 ≠ t2) (h1 : (D.tile t1).pts k1 = H) (h2 : (D.tile t2).pts k2 = H) (e1 : idx t1 k1 = l) (e2 : idx t2 k2 = l) :
    2 ≤ cnt D idx H l := by
  classical
  unfold cnt
  have : ({(t1, k1), (t2, k2)} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = H ∧ idx p.1 p.2 = l) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card this
  rw [Finset.card_pair (fun e => hne (congrArg Prod.fst e))] at h3
  exact h3

theorem cnt_one (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane} (l : Fin 3) {t : Fin N} {k : Fin 3}
    (h1 : (D.tile t).pts k = H) (e1 : idx t k = l) : 1 ≤ cnt D idx H l := by
  classical
  unfold cnt
  exact Finset.card_pos.mpr ⟨(t, k), by simp [h1, e1]⟩

theorem idx_two_of_cnt (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {H : Plane}
    (c0 : cnt D idx H 0 = 0) (c1 : cnt D idx H 1 = 0) {t : Fin N} {k : Fin 3} (h : (D.tile t).pts k = H) : idx t k = 2 := by
  by_contra hne
  have : idx t k = 0 ∨ idx t k = 1 := by
    generalize idx t k = z at hne
    revert z; decide
  rcases this with e | e
  · have := cnt_one D idx 0 h e; omega
  · have := cnt_one D idx 1 h e; omega

theorem no_contra_003 : ∀ a1 b1 a2 b2 a3 b3 : Fin 3, ((a1 = 0 ∧ b1 = 1) ∨ (a1 = 1 ∧ b1 = 0)) → ((a2 = 0 ∧ b2 = 1) ∨ (a2 = 1 ∧ b2 = 0)) →
    ((a3 = 0 ∧ b3 = 1) ∨ (a3 = 1 ∧ b3 = 0)) → (a1 = 0 ↔ b2 = 0) → (a2 = 0 ↔ b3 = 0) → ¬ (b1 = 1 ∧ a2 = 1) → ¬ (b2 = 1 ∧ a3 = 1) → False := by
  intro a1 b1 a2 b2 a3 b3
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one]
  have := a1.isLt; have := b1.isLt; have := a2.isLt; have := b2.isLt; have := a3.isLt; have := b3.isLt
  omega

/-- **Lemma 8.1 (iii)**: a tile vertex in the relative interior of a side of the target, from which no edge of `Γ_a ∪ Γ_k` starts, is `SideNormal`. -/
theorem sideNormal_of_noedge (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (harith : HalfPlaneArith D) {V : Plane} {m : Fin 3} (h0 : D.target.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < D.target.basis.coord j V) (hv : ∃ i k, (D.tile i).pts k = V)
    (hreg : cnt D idx V 0 = cnt D idx V 1)
    (hnoGa : ∀ H', ¬ GaEdge D.toDissection (slen D 0) V H') (hnoGk : ∀ Z, ¬ GkEdge D.toDissection idx V Z) :
    SideNormal D idx V := by
  classical
  obtain ⟨hStr0, hcls, hcard3⟩ := side_counts D idx hidxA harith h0 hpos hv hreg
  refine ⟨hcard3, ?_⟩
  intro pT p q s1 s2 s3 hF
  obtain ⟨hpT, hok, hloc, hspec, d12, d13, d23, hall, r1, r2, r3, r4⟩ := hF
  have hcorner : ∀ x : AtV D.toDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    by_contra hno
    push Not at hno
    have : x.1 ∈ Strn D.toDissection V := by
      simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hno⟩
    have := Finset.card_pos.mpr ⟨x.1, this⟩
    omega
  have hcr : ∀ x : AtV D.toDissection V, 0 < crs (p x) (q x) := fun x => crs_pos_of_corner (hok x) (hspec x) (hcorner x)
  -- positions relative to `pT`
  have c1 : 0 < crs pT (q s1) := by
    obtain ⟨a, ha, hap⟩ := r1.smul
    have h := hcr s1
    rw [hap] at h; unfold crs at h ⊢; try simp only at h ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg ha.le (neg_nonneg.mpr hX)]
  have c2 : 0 < crs pT (p s2) := ExtFan.crs_pos_of_par r2 c1
  have c3p : 0 < crs pT (p s3) := by
    obtain ⟨b, hb, hbq⟩ := r4.symm.smul
    have h := hcr s3
    rw [hbq] at h; unfold crs at h ⊢; try simp only at h ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hb.le (neg_nonneg.mpr hX)]
  have c3 : 0 < crs pT (q s2) := by
    obtain ⟨c, hc, hcp⟩ := r3.smul
    rw [hcp] at c3p; unfold crs at c3p ⊢; try simp only at c3p ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have arm_nonneg : ∀ x : AtV D.toDissection V, 0 ≤ crs pT (p x) ∧ 0 ≤ crs pT (q x) := by
    intro x
    rcases hall x with rfl | rfl | rfl
    · refine ⟨(ExtFan.crs_zero_of_par r1 (by unfold crs; ring)).ge, c1.le⟩
    · exact ⟨c2.le, c3.le⟩
    · exact ⟨c3p.le, (ExtFan.crs_zero_of_par r4.symm (by unfold crs; ring)).ge⟩
  have nbray : ∀ ρ : V2, 0 < crs pT ρ → NoBack D.toDissection ρ V := by
    intro ρ hρ
    apply noBack_of_none' p q hok hloc hspec
    intro x
    obtain ⟨h1, h2⟩ := arm_nonneg x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := ExtFan.crs_neg_of_par h hρ; linarith
    · have := ExtFan.crs_neg_of_par h hρ; linarith
  have nb1 := nbray _ c1
  have nb2 := nbray _ c3
  have iff1 : (nsq (q s1) = slen D 0 ^ 2 ↔ nsq (p s2) = slen D 0 ^ 2) := by
    by_contra hn
    have hx : (nsq (q s1) = slen D 0 ^ 2 ∧ nsq (p s2) ≠ slen D 0 ^ 2) ∨ (nsq (q s1) ≠ slen D 0 ^ 2 ∧ nsq (p s2) = slen D 0 ^ 2) := by tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray' D idx hidx hnc p q hok hspec s1 s2 (hcr s1) (hcr s2) r2 nb1 hx
    exact hnoGa H' hH'
  have iff2 : (nsq (q s2) = slen D 0 ^ 2 ↔ nsq (p s3) = slen D 0 ^ 2) := by
    by_contra hn
    have hx : (nsq (q s2) = slen D 0 ^ 2 ∧ nsq (p s3) ≠ slen D 0 ^ 2) ∨ (nsq (q s2) ≠ slen D 0 ^ 2 ∧ nsq (p s3) = slen D 0 ^ 2) := by tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray' D idx hidx hnc p q hok hspec s2 s3 (hcr s2) (hcr s3) r3 nb2 hx
    exact hnoGa H' hH'
  refine ⟨hcorner s2, ?_, iff1, iff2⟩
  intro k1 k2 k3 hk1 hk2 hk3
  rcases hcls with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · exfalso
    obtain ⟨kk1, fl1, hkk1, hp1, hq1⟩ := spec_corner_data (hspec s1) (hcorner s1)
    obtain ⟨kk2, fl2, hkk2, hp2, hq2⟩ := spec_corner_data (hspec s2) (hcorner s2)
    obtain ⟨kk3, fl3, hkk3, hp3, hq3⟩ := spec_corner_data (hspec s3) (hcorner s3)
    have g1 := idx_two_of_cnt D idx e0 e1 hkk1
    have g2 := idx_two_of_cnt D idx e0 e1 hkk2
    have g3 := idx_two_of_cnt D idx e0 e1 hkk3
    have u1 := arms_01 (idx s1.1) kk1 fl1 g1
    have u2 := arms_01 (idx s2.1) kk2 fl2 g2
    have u3 := arms_01 (idx s3.1) kk3 fl3 g3
    have f1 := (nsq_q_iff D idx hidx hab hac fl1 hkk1 hq1)
    have f2 := (nsq_p_iff D idx hidx hab hac fl2 hkk2 hp2)
    have f3 := (nsq_q_iff D idx hidx hab hac fl2 hkk2 hq2)
    have f4 := (nsq_p_iff D idx hidx hab hac fl3 hkk3 hp3)
    have k1' : ¬ (idx s1.1 (armQ kk1 fl1) = 1 ∧ idx s2.1 (armP kk2 fl2) = 1) := by
      rintro ⟨t1x, t1y⟩
      obtain ⟨Z, hZ⟩ := gk_of_ray' D idx hidx hab hac p q s1 s2 r2 d12 hkk1 hkk2 hp1 hq1 hp2 hq2 g1 t1x g2 t1y
      exact hnoGk Z hZ
    have k2' : ¬ (idx s2.1 (armQ kk2 fl2) = 1 ∧ idx s3.1 (armP kk3 fl3) = 1) := by
      rintro ⟨t1x, t1y⟩
      obtain ⟨Z, hZ⟩ := gk_of_ray' D idx hidx hab hac p q s2 s3 r3 d23 hkk2 hkk3 hp2 hq2 hp3 hq3 g2 t1x g3 t1y
      exact hnoGk Z hZ
    exact no_contra_003 _ _ _ _ _ _ u1 u2 u3 (by rw [← f1, ← f2]; exact iff1) (by rw [← f3, ← f4]; exact iff2) k1' k2'
  · have hk : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = V → ∀ l : Fin 3, idx t k = l → cnt D idx V l = 1 := by
      intro t k hk l hl
      have := cnt_one D idx l hk hl
      fin_cases l <;> simp_all
    refine ⟨?_, ?_, ?_⟩
    · intro e
      have := cnt_two D idx (idx s1.1 k1) (fun h => d12 (Subtype.ext h)) hk1 hk2 rfl e.symm
      have := hk _ _ hk1 _ rfl
      omega
    · intro e
      have := cnt_two D idx (idx s1.1 k1) (fun h => d13 (Subtype.ext h)) hk1 hk3 rfl e.symm
      have := hk _ _ hk1 _ rfl
      omega
    · intro e
      have := cnt_two D idx (idx s2.1 k2) (fun h => d23 (Subtype.ext h)) hk2 hk3 rfl e.symm
      have := hk _ _ hk2 _ rfl
      omega

/-- **Lemma 8.1 (iii) for a directed side**: every tiling vertex on the open side `X0 Y0` of the target is `SideNormal` — exactly the hypothesis `hnorm` of `lemma43_ii`. -/
theorem hnorm_of_lemma81 (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {w0 w1 w2 : ℕ} {u : ℝ} (W : WtData D w0 w1 w2 u)
    (hw3 : (w0, w1, w2) = (1, 7, 4) ∨ (w0, w1, w2) = (1, 19, 10) ∨ (w0, w1, w2) = (7, 13, 10))
    (hreg : ∀ P, (∃ i k, (D.tile i).pts k = P) → cnt D idx P 0 = cnt D idx P 1)
    {d : V2} {X0 Y0 : Plane} (hside : TriStep D.target d X0 Y0) :
    ∀ V, V ≠ X0 → V ≠ Y0 → (∃ j k, (D.tile j).pts k = V) → crs d (toV2 (V - X0)) = 0 → SideNormal D idx V := by
  intro V h1 h2 hv hline
  have hVT : V ∈ D.target.carrier := by
    obtain ⟨j, k, hk⟩ := hv
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨j, vertex_mem hk⟩
  obtain ⟨m, h0, hpos⟩ := open_side_of_triStep hside hVT hline h1 h2
  have hnot : V ∉ interior D.target.carrier := by
    rw [Tri.mem_interior_iff_coord_pos]
    intro h; exact absurd h0 (ne_of_gt (h m))
  have harith := halfPlaneArith_of_wt W
  exact sideNormal_of_noedge D idx hidx hidxA hnc hab hac harith h0 hpos hv (hreg V hv)
    (fun H' hH' => lemma81_ii D idx hidx hidxA hnc hab hac W hw3 hreg hnot (Or.inl hH'))
    (fun Z hZ => lemma81_ii D idx hidx hidxA hnc hab hac W hw3 hreg hnot (Or.inr hZ))

end Erdos634.Draft.LaczFormal.Graph
