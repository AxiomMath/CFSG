module

public import Certificates.Kernel.HS589207.M
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.BfsRecK

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HS589206.KChk

open CFSG.KC.DcHSOutK CFSG.KC.Enum CFSG.KD.HS589207

@[expose] noncomputable def K (i : Nat) : Nat → Nat :=
  CFSG.KC.E64F.wordF A (CFSG.Quasithin.H13.LocDbl.HSLoc.kWords.getD i [])

@[expose] noncomputable def uI (q : Nat) : Nat :=
  ((List.range 100).find? fun p => Nat.beq (uF p) q).getD 0

@[expose] noncomputable def fix01 (f : Nat → Nat) : Bool := Nat.beq (f 0) 0 && Nat.beq (f 1) 1

@[expose] noncomputable def cntBlk (b : Nat) (f : Nat → Bool) (len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l ih => Nat.add ih (cond (f (Nat.add b l)) 1 0)) len

@[expose] noncomputable def anyBlk (b : Nat) (f : Nat → Bool) (len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun l ih => f (Nat.add b l) || ih) len

@[expose] noncomputable def anyM (f : Nat → Bool) : Bool :=
  anyBlk 0 f 2880 || anyBlk 2880 f 2880 || anyBlk 5760 f 2880 || anyBlk 8640 f 2880

@[expose] def incB : List Nat → Bool
  | a :: b :: l => Nat.blt a b && incB (b :: l)
  | _ => true

@[expose] noncomputable def centT (m : Nat) : Bool :=
  !(commF (mF m) (K 0) && commF (mF m) (K 1)) || eqF (mF m) (fun q => q)

@[expose] noncomputable def centWT (m : Nat) : Bool :=
  !(commF (fun q => wF (mF m q)) (K 0) && commF (fun q => wF (mF m q)) (K 1))

@[expose] def inF0 (l : List Nat) : Bool :=
  l.all fun x => [0, 1, 5, 21, 39, 50, 53, 61].contains x

theorem pres : allN 2 (fun t => inF0 ([0, 1, 5, 21, 39, 50, 53, 61].map (GM t)) &&
    ((Nat.beq (GM t 0) 0 && Nat.beq (GM t 1) 1) || (Nat.beq (GM t 0) 1 && Nat.beq (GM t 1) 0))) =
    true := by
  quickRfl

theorem kcount : Nat.ble (cntBlk 0 (fun k => fix01 (mF k)) 2880 +
    cntBlk 2880 (fun k => fix01 (mF k)) 2880 + cntBlk 5760 (fun k => fix01 (mF k)) 2880 +
    cntBlk 8640 (fun k => fix01 (mF k)) 2880) 5760 = true := by
  quickRfl

theorem kfix : (ltF (K 0) && ltF (K 1) && fix01 (K 0) && fix01 (K 1)) = true := by quickRfl

theorem kmem : (anyM (fun k => eqF (mF k) (K 0)) && anyM (fun k => eqF (mF k) (K 1))) = true := by
  quickRfl

theorem uinv : (ltF uI && eqF (fun q => uF (uI q)) (fun q => q) && eqF (fun q => uI (uF q)) (fun q => q) &&
    (List.range 100).all (fun x =>
      ([0, 1, 5, 21, 39, 50, 53, 61].map gF).contains x ==
        ([0, 1, 5, 21, 39, 50, 53, 61].map uI).contains x)) = true := by
  quickRfl

theorem fsort : allN 3850 (fun i => incB (setT FR.TF i)) = true := by quickRfl

theorem c0 : allBlk 0 centT 2880 = true := by quickRfl

theorem c1 : allBlk 2880 centT 2880 = true := by quickRfl

theorem c2 : allBlk 5760 centT 2880 = true := by quickRfl

theorem c3 : allBlk 8640 centT 2880 = true := by quickRfl

theorem w0 : allBlk 0 centWT 2880 = true := by quickRfl

theorem w1 : allBlk 2880 centWT 2880 = true := by quickRfl

theorem w2 : allBlk 5760 centWT 2880 = true := by quickRfl

theorem w3 : allBlk 8640 centWT 2880 = true := by quickRfl

end CFSG.KD.HS589206.KChk

end
