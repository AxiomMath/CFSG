module

public import Certificates.Kernel.HS3850.UTDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.PkPow

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KC.PkPow
open CFSG.KLie.CT (fget)

theorem invs : ((List.range 1024).filter (fun i => !(Nat.beq (SY.E i) idn) &&
    (Nat.beq (img (SY.E i) (img (SY.E i) 0)) 0 && Nat.beq (img (SY.E i) (img (SY.E i) 5)) 5)) ==
    (List.range 191).map INV) = true := by quickRfl

theorem keys : allN 192 (fun i => allN i fun j => !(Nat.beq (kk (xE i)) (kk (xE j)))) = true := by
  quickRfl

theorem comm : allN 191 (fun i => allN 191 fun j => Bool.beq (Nat.testBit (CM i) j)
    (Nat.beq (img (X i) (img (X j) 0)) (img (X j) (img (X i) 0)) &&
      Nat.beq (img (X i) (img (X j) 5)) (img (X j) (img (X i) 5)))) = true := by quickRfl

theorem prodk : allN 191 (fun i => allN 191 fun j => bIf(Nat.testBit (CM i) j,
    Nat.ble (fget (PR i) j 8) 191 && Nat.beq (Nat.add (Nat.mul (img (X i) (img (X j) 0)) 4096)
      (img (X i) (img (X j) 5))) (kk (xE (fget (PR i) j 8))),
    Nat.beq (fget (PR i) j 8) 0)) = true := by quickRfl

@[expose] noncomputable def ucjK (i : Nat) : Bool :=
  Nat.blt (UCR i) 191 && Nat.beq (UCR (UCR i)) (UCR i) && Nat.beq (FX (UCR i)) (FX i) &&
    Nat.blt (UCJ i) 1024 && Nat.blt (UCI i) 1024 &&
    Nat.beq (img (X i) (img (SY.E (UCJ i)) 0)) (img (SY.E (UCJ i)) (img (X (UCR i)) 0)) &&
    Nat.beq (img (X i) (img (SY.E (UCJ i)) 5)) (img (SY.E (UCJ i)) (img (X (UCR i)) 5)) &&
    Nat.beq (img (SY.E (UCJ i)) (img (SY.E (UCI i)) 0)) 0 &&
    Nat.beq (img (SY.E (UCJ i)) (img (SY.E (UCI i)) 5)) 5 &&
    Nat.beq (img (SY.E (UCI i)) (img (SY.E (UCJ i)) 0)) 0 &&
    Nat.beq (img (SY.E (UCI i)) (img (SY.E (UCJ i)) 5)) 5

theorem fix : allN 191 (fun i => bIf(Nat.beq (UCR i) i, Nat.beq (nfix 3850 12 (X i)) (FX i),
    ucjK i)) = true := by quickRfl

end CertificateChecks.KernelHS3850.UT

end
