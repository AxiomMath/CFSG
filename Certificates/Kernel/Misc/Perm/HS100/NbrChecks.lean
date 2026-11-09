module

public import Certificates.Kernel.Misc.Perm.HS100.Base
public import Certificates.Kernel.Misc.Perm.HS100.S0Data
public import Certificates.Kernel.Misc.Perm.HS100.NbrData
public import Certificates.Data.Kernel.Misc.PermAdj
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Nbr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.PermAdj CertificateChecks.KernelMisc.HS100

@[expose] noncomputable def XN : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))
    (pcomp 100 7 (mask 7) (HX.F 0) (HX.F 15))

@[expose] noncomputable def XNI : Nat := pcomp 100 7 (mask 7) XN XN

@[expose] noncomputable def SRC (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (S0.UO.T (i - 5775)) (S0.ZO.T i) (Nat.blt i 5775)

@[expose] noncomputable def TT (i : Nat) : Nat := pcomp 100 7 (mask 7) XNI (SRC i)

@[expose] noncomputable def cube3K (p : Nat) : Bool :=
  Nat.beq (pcomp 100 7 (mask 7) p (pcomp 100 7 (mask 7) p p)) (pidn 100 7)

@[expose] noncomputable def selPt (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (!cube3K (TT i)) (cube3K (TT i))
    (Nat.blt (INVI i) 261 && Nat.beq (NBI (INVI i)) i)

@[expose] noncomputable def selSl (s : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul 1925 s) 1925 selPt

theorem hNBI : allN 261 (fun j => Nat.blt (NBI j) 21175 && Nat.beq (NLP j) (TT (NBI j)) &&
    cube3K (NLP j)) = true := by
  quickRfl

theorem cliqueI : allN 261 (cliquePt 100 7 261 XN NLP fun j => j) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Nbr

end

#kon_slices CertificateChecks.KernelMisc.HS100.Nbr.selSl 0 11
#kon_join CertificateChecks.KernelMisc.HS100.Nbr.selAll CertificateChecks.KernelMisc.HS100.Nbr.selSl 11
