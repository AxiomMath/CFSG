module

public import Certificates.Kernel.LocalQT.HSAutO.R4064
public import Certificates.Data.Kernel.PkPow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126
open CFSG.KD.LQT.HO CFSG.QuasithinUnique.Id2519.HSAut

@[expose] noncomputable def lc2 (j : Nat) : Nat := HC.F (Nat.add (nat_lit 13) j)

@[expose] noncomputable def fx (p : Nat) : Nat := nfix (nat_lit 3850) (nat_lit 12) p

theorem canon_hc : allN 43 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (HC.F k)) = true := by
  quickRfl

theorem ok22228 : strictB (pc (wfoldR lq e1Letters) (wfoldR lq e2Letters)) (fun W1 =>
    strictB (pc W1 W1) (fun W2 => strictB (pc W2 W1) (fun W3 =>
      bAnd(Nat.beq (pc W3 W3) idn, bAnd((Nat.beq W2 idn).not, (Nat.beq W3 idn).not))))) = true := by
  quickRfl

theorem ok23300 : strictB (wfoldR lc2 [0, 0, 1, 0]) (fun D =>
    bAnd(Nat.beq (pc D D) idn, bAnd((Nat.beq D idn).not,
      Nat.beq (fx (pc (HC.F 12) D)) 30))) = true := by
  quickRfl

theorem ok23004 : strictB (wfoldR lc2 [3, 0, 0, 3, 2]) (fun Y =>
    bAnd(Nat.beq (fx (HC.F 5)) 170, bAnd(Nat.beq (fx (HC.F 12)) 30,
    bAnd(Nat.beq (pc Y Y) idn, bAnd((Nat.beq Y idn).not,
    bAnd(Nat.beq (fx Y) 30, Nat.beq (fx (pc (HC.F 12) Y)) 30)))))) = true := by
  quickRfl

end CFSG.KD.HS3850

end
