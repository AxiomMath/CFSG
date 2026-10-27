module

public import Certificates.Kernel.HS3850.Small
public import Certificates.Data.Kernel.Spor.MulH
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126 CFSG.KS.MulH

@[expose] noncomputable def g12 (l : Nat) : Nat := HC.F ([6, 7, 13, 14, 15, 16].getD (Nat.sub l 1) 0)

@[expose] noncomputable def g4 (l : Nat) : Nat := HC.F (Nat.add (nat_lit 34) l)

@[expose] noncomputable def pw (p e : Nat) : Nat := ppw (nat_lit 3850) (nat_lit 12) p e

@[expose] noncomputable def ordK (p m : Nat) : Bool :=
  bAnd(Nat.beq (pw p m) idn,
    (CFSG.Sporadic.Schreier.Native.divParts m).all fun e => (Nat.beq (pw p e) idn).not)

@[expose] noncomputable def c0K : Nat := wfoldK 3850 12 (mask 12) g12 [1, 6, 1, 6, 2, 2] idn

@[expose] noncomputable def d0K : Nat := pc (pc (pc (HC.F 13) (HC.F 13)) (HC.F 14)) (HC.F 13)

@[expose] noncomputable def xK : Nat := wfoldK 3850 12 (mask 12) g4 [2] idn

@[expose] noncomputable def yK : Nat := wfoldK 3850 12 (mask 12) g4 [1, 3] idn

theorem ok23203 : strictB (pinvS 3850 12 (mask 12) c0K) (fun R =>
    bAnd(Nat.beq (pc d0K d0K) idn, bAnd((Nat.beq d0K idn).not,
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) R,
    bAnd(invEqK 3850 12 (mask 12) (3850 * 12) c0K R,
    bAnd(Nat.beq (pc (pc R (HC.F 12)) c0K) (pc (HC.F 12) d0K),
    bAnd(ordK xK 3, bAnd(ordK yK 5, ordK (pc xK yK) 6)))))))) = true := by
  quickRfl

end CFSG.KD.HS3850

end
