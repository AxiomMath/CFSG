module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Data.Kernel.LyOmega.Cent
public import Certificates.Data.Kernel.LyOmega.Base
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.LyY "Certificates/Kernel/Ly3085/Omega/data/yb_decls.items.gz" 2889 8735464934510361257
  T0 WCt[] WS0[] WS1[] WS2[] ZK[] ZP[] ZL[]

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LyY

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CFSG.KD.LyOm (SC R0 R1 Q0 Q1 RTl WYB)

@[expose] noncomputable def GR : Nat → Nat := pickL [R0, R1, Q0, Q1]

@[expose] noncomputable def Y : Nat := sWord SC GR SC.ONE WYB

@[expose] noncomputable def GC : Nat := sWord SC GR SC.ONE WCt

@[expose] noncomputable def GS : Nat → Nat :=
  pickL [sWord SC GR SC.ONE WS0, sWord SC GR SC.ONE WS1, sWord SC GR SC.ONE WS2]

theorem quad : bAnd(sVld SC T0, Nat.beq (sQuad SC 4 4 3 Y) T0) = true := by quickRfl

theorem conj : Nat.beq (sMul SC GC RTl) (sMul SC T0 GC) = true := by quickRfl

theorem cent : bAnd(Nat.beq (sMul SC (GS 0) T0) (sMul SC T0 (GS 0)),
    bAnd(Nat.beq (sMul SC (GS 1) T0) (sMul SC T0 (GS 1)),
      Nat.beq (sMul SC (GS 2) T0) (sMul SC T0 (GS 2)))) = true := by quickRfl

theorem tree : sConjTree SC GS (pickL ZK) (pickL ZP) (pickL ZL) Y 3 20 = true := by quickRfl

theorem neg_quad : notB (Nat.beq (sQuad SC 4 4 2 Y) T0) = true := by quickRfl

theorem neg_conj : notB (Nat.beq (sMul SC GC RTl) (sMul SC RTl GC)) = true := by quickRfl

theorem neg_tree_lab : notB (sConjTree SC GS (pickL ZK) (pickL ZP) (fun k => Nat.mod (Nat.succ (pickL ZL k)) 3)
    Y 3 20) = true := by quickRfl

theorem ctrl_tree_one : sConjTree SC (fun _ => SC.ONE) (pickL ZK) (fun _ => 0) (fun _ => 0) Y 1 1 = true := by
  quickRfl

theorem neg_tree_dup : notB (sConjTree SC (fun _ => SC.ONE) (fun _ => Y) (fun _ => 0) (fun _ => 0) Y 1 2) = true :=
  by quickRfl

theorem neg_tree_root : notB (sConjTree SC GS (pickL ZK) (pickL ZP) (pickL ZL) T0 3 20) = true := by quickRfl

end CFSG.KD.LyY

end
