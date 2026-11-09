module

public import Certificates.Data.Kernel.M24L2.L5
public import Certificates.Kernel.M24L2.Data
public import Certificates.Kernel.M24L2.DataC
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.M24L2.CodeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.L5R

private theorem any_filter_self {α : Type} (f g : α → Bool) (h : ∀ e, f e = true → g e = true) :
    ∀ W : List α, W.any f = (W.filter g).any f
  | [] => rfl
  | e :: W => by
    have ih := any_filter_self f g h W
    by_cases hf : f e = true
    · have hg := h e hf
      simp [List.filter_cons, hg, hf]
    · cases hg : g e <;> simp [List.filter_cons, hg, hf, ih]

private theorem fbLWit_filter (G p : Nat) (W : List ((Nat × Nat) × Nat)) (x y : Nat) :
    fbLWit G p W x y = fbLWit G p (W.filter fun e => Nat.beq e.1.1 x) x y := by
  unfold fbLWit
  rw [anyL_eq, anyL_eq]
  exact any_filter_self _ _ (fun e he => by
    simp only [Bool.and_eq_true] at he
    exact he.1.1.1.1) W

theorem fbLK_eqF (G p : Nat) (allowB : Bool) (Cd : List Nat) (W : List ((Nat × Nat) × Nat)) :
    fbLK G p allowB Cd W = allL (fun x => allL (fun y =>
      fbPairK G p allowB (W.filter fun e => Nat.beq e.1.1 x) x y) Cd) Cd := by
  unfold fbLK
  congr 1
  funext x
  congr 1
  funext y
  unfold fbPairK
  rw [fbLWit_filter G p W x y]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fbL1_ok : fbLK glMask (betaC 0) true cands1 fbW1 = true := by
  rw [fbLK_eqF]
  quickRfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fbL2_ok : fbLK glMask gamC false cands2 fbW2 = true := by
  rw [fbLK_eqF]
  quickRfl

@[expose] noncomputable def cdAK (k : Nat) : Bool := sliceL (candM (betaC 0) cands1) (glES.getD k [])

@[expose] noncomputable def cdBK (k : Nat) : Bool := sliceL (candM gamC cands2) (glES.getD k [])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each cdAK 0 20

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
#kc_each cdBK 0 20

end CertificateChecks.KernelM24L2
