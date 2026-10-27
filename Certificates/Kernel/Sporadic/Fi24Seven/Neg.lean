module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Seven.Data
public import Certificates.Data.Kernel.Spor.SlpPlan

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.KC.Ord

@[expose] noncomputable def ckT (W : List (List Nat)) (R' : Nat → Nat) (ins : List (Nat × Nat))
    (nodes : List Nat) (outs : List (Nat × Nat)) (eqs neqs : List (List Nat × List Nat)) : Bool :=
  chunkOK CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD (CFSG.KD.BrFi24.RB (nat_lit 23))
    (CFSG.KD.BrFi24.RB (nat_lit 24)) (R (nat_lit 0)) W R' ins nodes outs eqs neqs

theorem neg_out : notB (ckT W7 R [] [0] [(0, 3)] [] []) = true := by quickRfl

theorem neg_node : notB (ckT W7 R [] [2, 4] [(4, 1)] [] []) = true := by quickRfl

theorem neg_eq : notB (ckT W7 R [] [] [] [([2], [4])] []) = true := by quickRfl

theorem neg_ne : notB (ckT W7 R [] [] [] [] [([2], [2])]) = true := by quickRfl

theorem neg_order : notB (ckT [[6]] R [] [0] [] [] []) = true := by quickRfl

theorem neg_missing : notB (ckT W7 R [] [4] [] [] []) = true := by quickRfl

theorem neg_vld : notB (ckT W7 (fun _ => Nat.add 1 (Nat.shiftLeft 1 609961)) [(2, 5)] [] [] [] []) = true := by
  quickRfl

theorem neg_plan : notB (planOK nK nR nBase lyK (fun r => Nat.succ (pcR r)) pnR inK ouK) = true := by
  quickRfl

theorem neg_slp : notB (slpC [[6]] 0) = true := by quickRfl

end CFSG.KD.F24S

end
