import Erdos634.Refl.CheckE

/-! Refl/CheckR.lean -- chunked checker: `checkNodeR known` is `checkNodeE`, except that a *stub* node (`tauN = 0`, never a
    real node: real nodes have `0 < tauN`) is accepted iff the current configuration is literally one of the `known`
    configurations.  Each known configuration is then certified separately by `checkNodeE` on its own subtree
    (`checkNodeE_sound`), so the kernel check is split into chunks of bounded memory.  UNAUDITED. -/

namespace Refl

def ptEq (p q : Pt) : Bool := p.x == q.x && p.y == q.y && p.w == q.w
def triEq (s t : _root_.Tri) : Bool := ptEq s.a t.a && ptEq s.b t.b && ptEq s.c t.c
def cfgEq : List _root_.Tri → List _root_.Tri → Bool
  | [], [] => true
  | s :: ss, t :: ts => triEq s t && cfgEq ss ts
  | _, _ => false

def checkNodeR (I : Inst) (known : List (List _root_.Tri)) : Nat → List _root_.Tri → Node → Bool
  | 0, _, _ => false
  | fuel + 1, cfg, n =>
    if n.tauN == 0 then known.any (fun c => cfgEq c cfg)
    else nodeLocalOkE I cfg n && killsCheck I cfg n.v n.d n.kills I.pl (n.children)
      (fun c cfg' => checkNodeR I known fuel cfg' c)

def _root_.Inst.checkAllR (I : Inst) (known : List (List _root_.Tri)) (fuel : Nat) (n : Node) : Bool :=
  I.ok && checkNodeR I known fuel [] n

/-- a stub node (placeholder for a separately certified subtree) -/
def stubNode : Node :=
  ⟨pt 0 0 1, pt 0 0 1, Bsp.inf [], Bsp.inf [], 0, 1, [], ⟨true, 0, ⟨pt 0 0 1, pt 0 0 1, pt 0 0 1⟩⟩, [], []⟩

theorem cfgEq_eq : ∀ (a b : List _root_.Tri), cfgEq a b = true → a = b := by
  intro a
  induction a with
  | nil => intro b h; cases b <;> simp_all [cfgEq]
  | cons s ss ih =>
    intro b h
    cases b with
    | nil => simp [cfgEq] at h
    | cons t ts =>
      simp only [cfgEq, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have e := ih ts h2
      rw [e]
      rcases s with ⟨⟨x1, y1, w1⟩, ⟨x2, y2, w2⟩, ⟨x3, y3, w3⟩⟩
      rcases t with ⟨⟨x1', y1', w1'⟩, ⟨x2', y2', w2'⟩, ⟨x3', y3', w3'⟩⟩
      simp_all [triEq, ptEq]

end Refl
