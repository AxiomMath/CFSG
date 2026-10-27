module

public import Certificates.Kernel.PlusFactors.Checks
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermCheck
public import Certificates.Data.Kernel.BfsPinKeys

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPlusF

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem kTabInvol : allN 60 (fun i => allN 60 fun j =>
    Nat.beq (pg 6 (mask 6) (PE.G i) (pg 6 (mask 6) (PE.G i) j)) j) = true := by decide +kernel

theorem kTabKey : allN 60 (fun i => allN 60 fun j =>
    Nat.beq i j || !Nat.beq (CFSG.KC.BfsPin.pkeyK 60 6 plusBase (PE.G i))
      (CFSG.KC.BfsPin.pkeyK 60 6 plusBase (PE.G j))) = true := by decide +kernel

theorem kTabConj : allN 60 (fun i => allN 60 fun j =>
    Nat.blt (pg 6 (mask 6) (PE.G i) j) 60 &&
      Nat.beq (PE.G (pg 6 (mask 6) (PE.G i) j)) (cmp (PE.G i) (cmp (PE.G j) (PE.G i)))) = true := by
  decide +kernel

end CertificateChecks.KernelPlusF
