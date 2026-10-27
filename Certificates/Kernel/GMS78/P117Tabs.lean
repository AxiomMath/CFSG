module

public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Data.Kernel.GMS78RuP117
public import Certificates.Data.GMS78RuSPrimeCheck
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS CFSG.KLie.CT CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

@[expose] noncomputable def gamF (c : Nat) : Bool :=
  allN 256 fun c' => Nat.beq (gam c c').val (fget (sGamRow GT c) c' 3)

#lc_blocks gamB gamF 256 8

@[expose] noncomputable def dpF (i : Nat) : Bool :=
  (fun x y => andB (Nat.beq y.1 (Nat.land x 255)) (andB (Nat.beq y.2.val (Nat.shiftRight x 8))
      (Nat.blt y.1 256)))
    (fget (neGet 0 DPR (i / 256)) (i % 256) 11) (dPart (fin8Of (i / 256)) (i % 256))

#lc_blocks dpB dpF 2048 256

theorem linOK : allN 64 (fun i => Nat.beq (linApply (dCodeTab.getD (i / 8) linId) (fin8Of (i % 8))).val
    (fget LIN i 3)) = true := by quickRfl

theorem dmOK : allN 64 (fun i => Nat.beq (dMul (fin8Of (i / 8)) (fin8Of (i % 8))).val
    (fget DM i 3)) = true := by quickRfl

theorem do1OK : allN 64 (fun i => (dOvf (fin8Of (i / 8)) (fin8Of (i % 8))) ==
    Nat.beq (fget DO1 i 1) 1) = true := by quickRfl

end CertificateChecks.KernelGMS78.SD

end
