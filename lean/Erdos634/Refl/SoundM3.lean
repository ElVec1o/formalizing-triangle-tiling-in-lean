import Erdos634.Refl.SoundM1
import Erdos634.Refl.SoundM2

/-! Refl/SoundM3.lean -- `checkNodeM_sound`, `checkAllM_sound`: soundness of the free-branch-point checker
    `CheckM` (with subset stubs).  Assembly as in `SoundE4`, with `placement_completeness_cone` in place
    of `placement_completeness` and no `baseY` hypothesis. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane)

namespace Refl

theorem triEqM_eq (s t : _root_.Tri) (h : triEqM s t = true) : s = t := by
  rcases s with ⟨⟨x1, y1, w1⟩, ⟨x2, y2, w2⟩, ⟨x3, y3, w3⟩⟩
  rcases t with ⟨⟨x1', y1', w1'⟩, ⟨x2', y2', w2'⟩, ⟨x3', y3', w3'⟩⟩
  simp_all [triEqM, ptEqM]

theorem cfgSub_mem (c cfg : List _root_.Tri) (h : cfgSub c cfg = true) : ∀ t ∈ c, t ∈ cfg := by
  intro t ht
  have h1 := List.all_eq_true.mp h t ht
  obtain ⟨u, hu, he⟩ := List.any_eq_true.mp h1
  rw [triEqM_eq t u he]; exact hu

theorem checkNodeM_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2)
    (hI : I.ok = true) (known : List (List _root_.Tri))
    (hk : ∀ c ∈ known, Sound Dn I M c) :
    ∀ (fuel : Nat) (cfg : List _root_.Tri) (n : NodeM), (∀ t ∈ cfg, t.ok = true) →
      checkNodeM I known fuel cfg n = true → Sound Dn I M cfg := by
  obtain ⟨htok, hDpos, p1, p2, p3, p4, p5, p6, hpl, o1, o2, o3, o4, o5, o6⟩ := Inst_ok_facts I hI
  intro fuel
  induction fuel with
  | zero => intro cfg n _ h; simp [checkNodeM] at h
  | succ fuel ih =>
    intro cfg n hcfgok hchk N D htg hm hreal
    classical
    by_cases hst : (n.tauN == 0) = true
    · simp only [checkNodeM, hst, if_true] at hchk
      obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp hchk
      exact hk c hc D htg hm (fun t ht => hreal t (cfgSub_mem c cfg hce t ht))
    have hne : (n.tauN == 0) = false := by simpa using hst
    simp only [checkNodeM, hne, Bool.false_eq_true, if_false, Bool.and_eq_true] at hchk
    obtain ⟨hloc, hkills⟩ := hchk
    have F := nodeLocalOkM_facts I cfg n hloc
    set S : Finset (Fin N) := Finset.univ.filter (fun i => ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn) with hSdef
    have hS : ∀ t ∈ cfg, ∃ i ∈ S, (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hi⟩ := hreal t ht
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hi⟩, hi⟩
    have hSt : ∀ i ∈ S, ∃ t ∈ cfg, (D.tile i).carrier = t.carr Dn := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hcone := cone_soundM Dn hD I htok cfg hcfgok n F D htg S hS
    have hfree := hfree_soundM Dn hD I hDn htok cfg hcfgok n F D htg S hSt
    have hdg := dg_re Dn hD I cfg n F
    have hunit := unit_re Dn hD I hDn n.d F.dw F.unit
    obtain ⟨j, hjS, k0, k1, k2, h01, h02, h12, hk0, ⟨c', hc', hk1⟩, hk2⟩ :=
      placement_completeness_cone D.toDissection S (n.v.re Dn) (n.d.re Dn) (n.g.re Dn) hunit hdg
        hcone hfree
    have hcong : (D.tile j).Congruent M := (D.tiles_congruent j).trans hm
    have hsix := six_placements hcong hMa hMb hMc hunit h01 h02 h12 hk0 hc' hk1 hk2
    -- the numerics of every placement
    have hpos : ∀ p ∈ I.pl, 0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn := by
      intro p hp
      rw [hpl] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · have := placeOk_facts I _ _ _ _ o1; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o2; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o3; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o4; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o5; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
      · have := placeOk_facts I _ _ _ _ o6; exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩
    -- one of the six placements is realised by tile `j`
    have hrealj : ∃ p ∈ I.pl, (D.tile j).carrier = (placeTri I n.v n.d p).carr Dn := by
      have key := fun (l1 l2 l3 : Int) (p : Place) (hp : placeOk I l1 l2 l3 p = true)
          (h1 : (D.tile j).pts k1 = n.v.re Dn + (l1 : ℝ) • n.d.re Dn)
          (h2 : (D.tile j).pts k2 = placeThird (n.v.re Dn) (n.d.re Dn) l1 l2 l3) =>
        place_sound Dn hD I hDn n.v n.d F.vw F.dw F.unit l1 l2 l3 p hp (D.tile j) h01 h02 h12 hk0 h1 h2
      rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨p1, by simp [hpl], key _ _ _ p1 o1 h1 h2⟩
      · exact ⟨p2, by simp [hpl], key _ _ _ p2 o2 h1 h2⟩
      · exact ⟨p3, by simp [hpl], key _ _ _ p3 o3 h1 h2⟩
      · exact ⟨p4, by simp [hpl], key _ _ _ p4 o4 h1 h2⟩
      · exact ⟨p5, by simp [hpl], key _ _ _ p5 o5 h1 h2⟩
      · exact ⟨p6, by simp [hpl], key _ _ _ p6 o6 h1 h2⟩
    obtain ⟨pj, hpj, hjc⟩ := hrealj
    have hreal' : ∀ t ∈ cfg, ∃ i, i ≠ j ∧ (D.tile i).carrier = t.carr Dn := by
      intro t ht
      obtain ⟨i, hiS, hi⟩ := hS t ht
      exact ⟨i, fun h => hjS (h ▸ hiS), hi⟩
    refine killsSoundM Dn hD I hDn htok n.v n.d F.vw F.dw F.unit cfg hcfgok D htg j hreal'
      (fun c cfg' => checkNodeM I known fuel cfg' c) n.kills I.pl n.children hpos ?_ hkills pj hpj hjc
    intro c p hp hrec hj
    obtain ⟨pl1, ppd, pqd, pqn⟩ := hpos p hp
    have htri := placeTri_ok I n.v n.d p F.vw F.dw F.unit hDpos pl1 ppd pqd pqn
    refine ih (cfg ++ [placeTri I n.v n.d p]) c ?_ hrec D htg hm ?_
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hcfgok t h
      · simp only [List.mem_singleton] at h; subst h; exact htri
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hreal t h
      · simp only [List.mem_singleton] at h; subst h; exact ⟨j, hj⟩

#print axioms Refl.checkNodeM_sound

theorem checkAllM_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (M : Erdos634.Geometry.Tri)
    (hMa : dist (M.pts 0) (M.pts 1) = I.sides.1) (hMb : dist (M.pts 1) (M.pts 2) = I.sides.2.1)
    (hMc : dist (M.pts 0) (M.pts 2) = I.sides.2.2) (known : List (List _root_.Tri))
    (hk : ∀ c ∈ known, Sound Dn I M c) (fuel : Nat) (n : NodeM)
    (h : I.checkAllM known fuel n = true) : Sound Dn I M [] := by
  unfold Inst.checkAllM at h
  simp only [Bool.and_eq_true] at h
  exact checkNodeM_sound Dn hD I hDn M hMa hMb hMc h.1 known hk fuel [] n (by simp) h.2

#print axioms Refl.checkAllM_sound

end Refl
