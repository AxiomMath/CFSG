module

public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Kernel.MinusFrame.Data
public import Certificates.Data.Kernel.PermPinK
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermPinK
open CFSG.OddTranspositions.PartThree.MinusFrame CertificateChecks.KernelMinusEnum

theorem kBindX : (bindArrK (tArr ()) 65 7 (XT 0) && bindArrK xArr 65 7 (XT 1) &&
    Nat.beq t0Gens.size 3 && allN 3 (fun k => bindArrK t0Gens[k]! 65 7 (XT (k + 2)))) = true := by
  quickRfl

theorem kCanonX : allN 5 (fun k => canonK 65 7 (mask 7) (Nat.mul 65 7) (XT k)) = true := by
  quickRfl

theorem kMemX : allN 4 (fun k => memK 15600 ME.T (XT (k + 1))) = true := by quickRfl

theorem kStab : stabK 65 7 centArr.toList 15600 ME.T (XT 0) = true := by quickRfl

theorem kCard : Nat.beq (centCnt 65 7 15600 ME.T (XT 0)) 240 = true := by quickRfl

end CertificateChecks.KernelMinusFrame

end
