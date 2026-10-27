module

public import Certificates.Data.Kernel.U43Mod.Aut3962
public import Certificates.Data.Kernel.U43Mod.Defs
public import Certificates.Data.Kernel.Multipliers.BindList
public import Certificates.Kernel.U43Mod.Data3962
public import Certificates.Kernel.Multipliers.U43BChain
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Aut3962

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Aut3962 CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelU43B
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

@[expose] def bs : List Nat := [0, 1, 9]

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def hiZ (p : Nat) : Bool := Nat.beq (Nat.shiftRight p (820 * 10)) 0

@[expose] noncomputable def inN (p : Nat) : Bool :=
  siftK 820 10 (mask 10) (820 * 10) (pidn 820 10) C.LR C.TRI C.BP 3 0 p

@[expose] noncomputable def outN (p : Nat) : Bool := bAnd(hiZ p, bIf(inN p, false, true))

@[expose] noncomputable def dPow (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 820 10) (fun _ ih => pc (DT 0) ih) m

@[expose] noncomputable def wa (ws : List Nat) (q : Nat) : Nat :=
  mwv 10 (mask 10) (C.S 0) (C.S 1) (C.SI 0) (C.SI 1) ws q

@[expose] noncomputable def waI (ws : List Nat) (q : Nat) : Nat :=
  mwvI 10 (mask 10) (C.S 0) (C.S 1) (C.SI 0) (C.SI 1) ws q

@[expose] noncomputable def cg (i j : Nat) : List Nat × List Nat :=
  lSel ([], []) (lSel (0, []) U43Aut.cenGens i).2 j

@[expose] noncomputable def bp (i : Nat) : Nat := (lSel (0, []) U43Aut.cenGens i).1

@[expose] noncomputable def stabPt (gt : List Nat × List Nat) (q : Nat) : Nat := waI gt.2 (wa gt.1 q)

@[expose] noncomputable def tBase (e : Nat × List Nat) : Nat := nIf(Nat.beq e.1 0, 0, 4)

theorem kBind : bAnd(CFSG.KC.BindList.bindListK 10 (mask 10) (DT 0) U43Aut.dTab.toList 0,
    CFSG.KC.BindList.bindListK 10 (mask 10) (DT 1) U43Aut.sTab.toList 0) = true := by
  quickRfl

theorem kPerm : allN 2 (fun j => permOK 820 10 (mask 10) (820 * 10) (DT j) (DTI j)) = true := by
  quickRfl

theorem kConj : allN 2 (fun j => allN 2 (fun i => inN (pc (pc (DT j) (C.S i)) (DTI j)))) = true := by
  quickRfl

theorem kD4 : Nat.beq (pc (DT 0) (dPow 3)) (pidn 820 10) = true := by quickRfl

theorem kOut : allN 4 (fun m => bAnd(bIf(Nat.beq m 0, true, outN (dPow m)),
    outN (pc (dPow m) (DT 1)))) = true := by
  quickRfl

theorem kCen : allN 4 (fun k => strictB (ZT k) (fun z =>
    strictB (Nat.shiftRight k 1) (fun i => strictB (Nat.land k 1) (fun j =>
      bAnd(permOK 820 10 (mask 10) (820 * 10) z (ZTI k), bAnd(inN z,
        bAnd(baseEq bs (pg 10 (mask 10) z) (stabPt (cg i j)),
          Nat.beq (pg 10 (mask 10) z (bp i)) (bp i)))))))) = true := by
  quickRfl

theorem kFix : allN 2 (fun i => strictB (bp i) (fun b =>
    strictB (ZT (Nat.mul 2 i)) (fun z0 => strictB (ZT (Nat.succ (Nat.mul 2 i))) (fun z1 =>
      allN 820 (fun q => bIf(bAnd(Nat.beq (pg 10 (mask 10) z0 q) q,
        Nat.beq (pg 10 (mask 10) z1 q) q), Nat.beq q b, true)))))) = true := by
  quickRfl

theorem kTrans : allIdx (fun e r => Nat.beq (wa e.2 (tBase e)) r) U43Aut.trans 0 = true := by
  quickRfl

end CertificateChecks.KernelU43Aut3962

end
