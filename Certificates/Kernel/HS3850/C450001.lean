module

public import Certificates.Kernel.HS3850.D450001
public import Certificates.Kernel.HS3850.Small
public import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850.T450001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126

@[expose] noncomputable def lb (l : Nat) : Nat := HC.F (Nat.add (nat_lit 21) l)

@[expose] noncomputable def ckK (s : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) false EK.G EK.GI 3 EK.cnt EK.T EK.PL EK.POS EK.SRT EK.SRI
    (Nat.mul s (nat_lit 32)) (nat_lit 32)

theorem hd_ok : bAnd(Nat.beq EK.cnt 720, bAnd(penumHdK idn EK.cnt 720 EK.T EK.PL,
    bAnd(Nat.beq (EK.G 0) (wfoldR lb [0]), bAnd(Nat.beq (EK.G 1) (wfoldR lb [4, 1]),
    bAnd(Nat.beq (EK.G 2) (wfoldR lb [3, 4, 1, 3, 2]),
    bAnd(Nat.beq (wfoldR lb [3, 2, 4, 3, 4, 2, 4, 1, 3]) (HC.F 32),
    bAnd(Nat.beq (pc (pc (HC.F 32) (HC.F 32)) (HC.F 32)) idn,
    bAnd((Nat.beq (HC.F 32) idn).not,
      allN 3 (fun j => Nat.beq (pc (HC.F 32) (EK.G j)) (pc (EK.G j) (HC.F 32))))))))))) = true := by
  quickRfl

end CFSG.KD.HS3850.T450001

end
