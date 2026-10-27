module

public import Certificates.Kernel.Sporadic.Tits.LocS
public import Certificates.Kernel.Sporadic.Tits.LocH
public import Certificates.Kernel.Sporadic.Tits.LocN
public import Certificates.Kernel.Sporadic.Tits.LocK
public import Certificates.Kernel.Misc.Tits.JTab8073
public import Certificates.Kernel.Misc.Tits.Pi7092
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsPS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open CertificateChecks.KernelMisc.TitsJT (siftJ G GI)

@[expose] noncomputable def Pi : Nat := CertificateChecks.KernelMisc.TitsPi.P

@[expose] noncomputable def PiI : Nat := pinvS 1755 11 (mask 11) Pi

@[expose] noncomputable def cj (A : Nat) : Nat :=
  pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) Pi A) PiI

@[expose] noncomputable def sift5 (LR TRI : Nat → Nat) (BP G : Nat) : Bool :=
  siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) LR TRI BP 5 0 G

theorem sS : allN 3 (fun i => sift5 TitsS.LR TitsS.TRI TitsS.BP (cj (TitsS.S i))) = true := by
  quickRfl
theorem sH : allN 3 (fun i => sift5 TitsH.LR TitsH.TRI TitsH.BP (cj (TitsH.S i))) = true := by
  quickRfl
theorem sN : allN 4 (fun i => sift5 TitsN.LR TitsN.TRI TitsN.BP (cj (TitsN.S i))) = true := by
  quickRfl
theorem sK : allN 2 (fun i => sift5 TitsK.LR TitsK.TRI TitsK.BP (cj (TitsK.S i))) = true := by
  quickRfl
theorem sJ : allN 4 (fun i => siftJ (cj (TitsJ.S i))) = true := by quickRfl

theorem sq : siftJ (pcomp 1755 11 (mask 11) Pi Pi) = true := by quickRfl

theorem sT : allN 3 (fun k => siftJ (pcomp 1755 11 (mask 11)
    (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (G k) Pi) (GI k)) PiI)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.TitsPS

end
