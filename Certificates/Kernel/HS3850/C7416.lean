module

public import Certificates.Kernel.HS3850.Fus
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KC.PkPow CFSG.KD.LQT.C4126

@[expose] noncomputable def hsIvK (t : Nat) : Bool :=
  bAnd(Nat.beq (pc t t) idn, (Nat.beq t idn).not)

@[expose] noncomputable def hsPairK (r s m t x : Nat) : Bool :=
  bAnd(strictB (pc t x) (fun P => ordK P r),
    strictB (List.foldr pc x (t :: x :: t :: List.replicate (m - 2) x)) (fun Q => ordK Q s))

theorem ok7416 : bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HS.F 0),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (HS.F 1),
    bAnd(hsIvK (HC.F 12), bAnd(hsIvK (HC.F 21), bAnd(hsIvK (HC.F 34),
    bAnd(hsPairK 6 3 2 (HC.F 12) (HS.F 0), bAnd(hsPairK 8 6 5 (HC.F 12) (HS.F 1),
    bAnd(hsPairK 6 3 2 (HC.F 21) (HS.F 0), bAnd(hsPairK 8 3 5 (HC.F 21) (HS.F 1),
    bAnd(hsPairK 6 3 2 (HC.F 34) (HS.F 0),
      hsPairK 30 10 5 (HC.F 34) (HS.F 1))))))))))) = true := by
  quickRfl

end CFSG.KD.HS3850

end
