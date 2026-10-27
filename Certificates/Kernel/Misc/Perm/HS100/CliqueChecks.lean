module

public import Certificates.Kernel.Misc.Perm.HS100.Base
public import Certificates.Kernel.Misc.Perm.HS100.Class3A
public import Certificates.Kernel.Misc.Perm.HS100.CliqueData
public import Certificates.Data.Kernel.Misc.PermAdj
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Clique

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.PermAdj CertificateChecks.KernelMisc.HS100

@[expose] noncomputable def X3 : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))
    (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))

@[expose] noncomputable def nbrSl (s : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 1600 s) 1600 (nbrPt 100 7 261 X3 K3.T NB INV)

theorem nums : (Nat.beq K3.ng 3 && Nat.beq K3.N 123200 && Nat.beq (K3.G 0) (HX.F 0) &&
    Nat.beq (K3.G 1) (HX.F 1) && Nat.beq (K3.G 2) (HX.F 15) && Nat.beq (K3.T K3.r0) X3) = true := by
  quickRfl

theorem hNB : allN 261 (nbPt 100 7 K3.N X3 K3.T NB) = true := by quickRfl

theorem clique : allN 261 (cliquePt 100 7 261 X3 K3.T NB) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Clique

end

#kon_slices CertificateChecks.KernelMisc.HS100.Clique.nbrSl 0 77
#kon_join CertificateChecks.KernelMisc.HS100.Clique.nbrAll CertificateChecks.KernelMisc.HS100.Clique.nbrSl 77
