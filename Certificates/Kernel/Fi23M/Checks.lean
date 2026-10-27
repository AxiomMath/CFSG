module

public import CFSG.Certificates.Kernel.Orders.Cert3
public import Certificates.Data.Kernel.Spor.WordProg
public import Certificates.Kernel.Fi23M.Data
public import Certificates.Kernel.Sporadic.Fi23Br.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_repo #kc_json_gz CFSG.KD.Fi23M "Certificates/Kernel/Fi23M/data/seed.json.gz" 1677
  18006990152749349976 (DA1 : List Nat) (DA2 : List Nat)

public noncomputable section

namespace CFSG.KD.Fi23M

theorem consts : CFSG.KC.Ord.consts3OK (nat_lit 253) (nat_lit 9) (nat_lit 64009) LO RM CI ONE UP =
    true := by
  quickRfl

theorem hroots : CFSG.KC.Ord.rootsOK RB VLD (nat_lit 1) (nat_lit 3) = true := by quickRfl

theorem iv0 : CFSG.KC.Ord.andB (VLD (RB (Nat.add (Nat.succ (nat_lit 2)) (nat_lit 0))))
    (Nat.beq (MUL (RB (Nat.succ (nat_lit 0))) (RB (Nat.add (Nat.succ (nat_lit 2)) (nat_lit 0)))) ONE) =
    true := by
  quickRfl

theorem iv1 : CFSG.KC.Ord.andB (VLD (RB (Nat.add (Nat.succ (nat_lit 2)) (nat_lit 1))))
    (Nat.beq (MUL (RB (Nat.succ (nat_lit 1))) (RB (Nat.add (Nat.succ (nat_lit 2)) (nat_lit 1)))) ONE) =
    true := by
  quickRfl

theorem b2 : Nat.beq (MUL (RB (nat_lit 2)) (RB (nat_lit 2))) (RB (nat_lit 4)) = true := by quickRfl

@[expose] def sC (k : Nat) : Bool := CFSG.KC.Ord.progOK RB 2 RS MUL ONE (PS k) (RS k)

@[expose] def rC (j : Nat) : Bool := CFSG.KC.Ord.progOK RB 2 RS MUL ONE (PR j) ONE

theorem nA : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RB (nat_lit 1)) ONE) = true := by
  quickRfl

theorem nB : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RB (nat_lit 2)) ONE) = true := by
  quickRfl

theorem nD : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS (nat_lit 1)) ONE) = true := by
  quickRfl

theorem nP1 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS (nat_lit 8)) ONE) = true := by
  quickRfl

theorem nP2 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (RS (nat_lit 9)) ONE) = true := by
  quickRfl

@[expose] def dL (k : Nat) : List Nat := List.range' (32 * k) (min 32 (255 - 32 * k))

@[expose] def d1C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun3 CFSG.KD.BrFi23.P1 256 65042 253 64009 RM (RB 1) (dL k)
    (DA1.getD k 0)) (DA1.getD (k + 1) 0)

@[expose] def d2C (k : Nat) : Bool :=
  Nat.beq (CFSG.KC.Ord.decRun3 CFSG.KD.BrFi23.P2 256 65042 253 64009 RM (RB 2) (dL k)
    (DA2.getD k 0)) (DA2.getD (k + 1) 0)

theorem d1_end : CFSG.KC.Ord.seedDone (nat_lit 253) VLD (RB (nat_lit 1)) (nat_lit 256039) = true := by
  quickRfl

theorem d2_end : CFSG.KC.Ord.seedDone (nat_lit 253) VLD (RB (nat_lit 2)) (nat_lit 256039) = true := by
  quickRfl

end CFSG.KD.Fi23M

#kc_each CFSG.KD.Fi23M.sC 0 10

#kc_each CFSG.KD.Fi23M.rC 0 5

#kc_each CFSG.KD.Fi23M.d1C 0 8

#kc_each CFSG.KD.Fi23M.d2C 0 8

namespace CFSG.KD.Fi23M

#kc_forall_chunks S.all (fun k => sC k = true) 10 CFSG.KD.Fi23M.sC 1

#kc_forall_chunks R.all (fun j => rC j = true) 5 CFSG.KD.Fi23M.rC 1

#kc_forall_chunks D1.all (fun k => d1C k = true) 8 CFSG.KD.Fi23M.d1C 1

#kc_forall_chunks D2.all (fun k => d2C k = true) 8 CFSG.KD.Fi23M.d2C 1

end CFSG.KD.Fi23M

end
