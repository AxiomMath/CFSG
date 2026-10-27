module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Seven.DataI

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.KC.Ord

theorem negI_even : notB (CKI (nat_lit 107)) = true := by quickRfl

theorem negI_prod : notB (invOut CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD
    (fun r => nIf(Nat.beq r (nat_lit 825), R (nat_lit 827), R r)) nR pcR pnR lyK nBase (nat_lit 108)
    (nat_lit 2175, nat_lit 826)) = true := by quickRfl

theorem negI_eq : notB (invOK CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD R nR pcR pnR lyK
    nBase (nat_lit 108) (ouK (nat_lit 108)) [([], [])] []) = true := by quickRfl

theorem negI_node : notB (invOK CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE CFSG.KD.BrFi24.VLD R nR pcR pnR lyK
    nBase (nat_lit 110) [(nat_lit 2177, nat_lit 826)] [] []) = true := by quickRfl

theorem negI_gen : notB (Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB (nat_lit 24))
    (CFSG.KD.BrFi24.RB (nat_lit 24))) CFSG.KD.BrFi24.ONE) = true := by quickRfl

end CFSG.KD.F24S

end
