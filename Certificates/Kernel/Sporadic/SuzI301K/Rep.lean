module

public import Certificates.Kernel.Sporadic.SuzI301K.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KD.SuzI301

@[expose] noncomputable def segLen (s : Nat) : Nat := nIf(Nat.blt s 50, 1024, 640)

@[expose] noncomputable def ch810302seg (s : Nat) : Bool :=
  segK TB GT 11 N (RW s) (Nat.shiftLeft s 10) (segLen s)

theorem kHead : headK TB GW GT N = true := by quickRfl

theorem kOrd : ordK TB N ORD = true := by quickRfl

theorem kInv : invK TB (nthN HW 0) (nthN HW 1) 0 N = true := by quickRfl

end CertificateChecks.KernelSpor.SuzI301K

set_option Elab.async false

#kc_each CertificateChecks.KernelSpor.SuzI301K.ch810302seg 0 51

namespace CertificateChecks.KernelSpor.SuzI301K

#kc_forall_tree segAll (fun s => ch810302seg s = true) 51
  CertificateChecks.KernelSpor.SuzI301K.ch810302seg

end CertificateChecks.KernelSpor.SuzI301K

end
