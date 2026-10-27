module

public import Certificates.Kernel.Fi23P.Small
public import Certificates.Data.Kernel.Fi23R.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K

set_option Elab.async false

@[expose] noncomputable def TG8 (k x : Nat) : Nat := nIf(Nat.beq k (nat_lit 9), tb G (nat_lit 8) x, tb G k x)

theorem neg_gen : Bool.not (allN (nat_lit 255)
    (bfsAt TG8 rtP offP labP genP parP posP ptsP)) = true := by quickRfl

@[expose] noncomputable def par2 (x : Nat) : Nat := parP (parP x)

theorem neg_par : Bool.not (allN (nat_lit 2048)
    (bfsAt TG rtP offP labP genP par2 posP ptsP)) = true := by quickRfl

@[expose] noncomputable def lab1 (x : Nat) : Nat := Nat.add (labP x) (nat_lit 1)

theorem neg_lab : Bool.not (bfsHd rtP offP lab1 posP) = true := by quickRfl

theorem neg_word : Bool.not (Bool.not (Nat.beq (wS (nat_lit 7) (ptsP (nat_lit 265)))
    (ptsP (nat_lit 265)))) = true := by quickRfl

@[expose] noncomputable def dep0 (_ : Nat) : Nat := nat_lit 0

theorem neg_dep : Bool.not (depAt rtP labP parP dep0 (ptsP (nat_lit 1))) = true := by quickRfl

theorem neg_trans : Bool.not (allN 255 (fun i => strictB (tb L 7 i) fun q =>
    Nat.beq (tb L 5 (tb G 8 q)) (tau (tb L 5 (piL.getD 8 0)) (tb L 5 q)))) = true := by quickRfl

theorem neg_cnt : Bool.not (Nat.beq (CFSG.KC.Fi23R.cntS (fun p => Nat.beq (labP p) (nat_lit 0))
    (nat_lit 0) (nat_lit 31671)) (nat_lit 254)) = true := by quickRfl

theorem neg_comm : Bool.not (Nat.beq (sigL.countP fun p => commK p 16688) 127) = true := by
  quickRfl

end CFSG.KD.Fi23P

end
