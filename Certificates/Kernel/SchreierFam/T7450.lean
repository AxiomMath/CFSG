module

public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.Misc.Tits.Text
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSchreierFam.T7450

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
  CertificateChecks.KernelMisc

@[expose] def w7450 : List Int := [4, 3, 4, 1, 4, 3, -4]

@[expose] noncomputable def FI (j : Nat) : Nat := pinvS 1755 11 (mask 11) (TitsText.F j)

@[expose] noncomputable def T : Nat :=
  wordK 1755 11 (mask 11) (pidn 1755 11) TitsText.F FI w7450

theorem wordT : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsText.F FI 4 w7450 T = true := by
  quickRfl

theorem rangeT : allN 1755 (fun i => Nat.blt (pg 11 (mask 11) T i) 1755) = true := by quickRfl

theorem highT : Nat.beq (Nat.shiftRight T (1755 * 11)) 0 = true := by quickRfl

theorem siftOK :
    siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 T = true := by
  quickRfl

end CertificateChecks.KernelSchreierFam.T7450
