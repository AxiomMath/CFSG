module

public import Certificates.Kernel.HSStd.M12PinData
public import Certificates.Data.Kernel.L34Cover
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelHSStd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Inv
open CFSG.EvenSporadicStandard.HSStd.HFI
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def M12.pr (s : Nat) : Bool :=
  pinSl 12 6 2 M12.G M12.T M12.E M12.C M12.S M12.SI 95040 1440 17 s

@[expose] noncomputable def M12.cv (s : Nat) : Bool :=
  covSl 12 6 M12.T M12O.T M12O.N 2 M12.W 1440 s

@[expose] noncomputable def M12C.cs (s : Nat) : Bool := centSl 12 6 M12.T (M12A.T 0) 1440 M12C.CC s

end CertificateChecks.KernelHSStd

#kon_slices CertificateChecks.KernelHSStd.M12.pr 0 66
#kon_join CertificateChecks.KernelHSStd.M12.prAll CertificateChecks.KernelHSStd.M12.pr 66
#kon_slices CertificateChecks.KernelHSStd.M12.cv 0 66
#kon_join CertificateChecks.KernelHSStd.M12.cvAll CertificateChecks.KernelHSStd.M12.cv 66
#kon_slices CertificateChecks.KernelHSStd.M12C.cs 0 66
#kon_join CertificateChecks.KernelHSStd.M12C.csAll CertificateChecks.KernelHSStd.M12C.cs 66

namespace CertificateChecks.KernelHSStd.M12K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Inv
open CFSG.EvenSporadicStandard.HSStd.HFI CertificateChecks.KernelHSStd
open CFSG.KLie.CT (andB orB notB)

theorem kBind : (Nat.beq m12Gens.size 2 && allN 2 fun k => bindArrK m12Gens[k]! 12 6 (M12.G k)) =
    true := by quickRfl

theorem kBindAB : (bindArrK m12a₀T 12 6 (M12A.T 0) && bindArrK m12b₀T 12 6 (M12B.T 0)) = true := by
  quickRfl

theorem kPerm : allN 2 (fun k => permOK 12 6 (mask 6) (12 * 6) (M12.G k)
    (pinvS 12 6 (mask 6) (M12.G k))) = true := by quickRfl

theorem kHead : headK 12 6 2 M12.G M12.T M12.C 66 95040 (pidn 12 6) = true := by quickRfl

theorem kOrbA : orbK 12 6 2 M12.G M12.GI M12A.T M12A.E M12A.S M12A.SI 396 10 (M12A.T 0) = true := by
  quickRfl

theorem kOrbB : orbK 12 6 2 M12.G M12.GI M12B.T M12B.E M12B.S M12B.SI 495 10 (M12B.T 0) = true := by
  quickRfl

theorem kAB : (Nat.blt (M12.AB 0) 95040 && Nat.beq (M12.T (M12.AB 0)) (M12A.T 0) &&
    Nat.blt (M12.AB 1) 95040 && Nat.beq (M12.T (M12.AB 1)) (M12B.T 0) &&
    Nat.beq (pcomp 12 6 (mask 6) (M12A.T 0) (M12A.T 0)) (pidn 12 6) &&
    !Nat.beq (M12A.T 0) (pidn 12 6) &&
    Nat.beq (pcomp 12 6 (mask 6) (M12B.T 0) (M12B.T 0)) (pidn 12 6) &&
    !Nat.beq (M12B.T 0) (pidn 12 6)) = true := by quickRfl

theorem kEnds : (Nat.beq (M12C.CC 0) 0 && Nat.beq (M12C.CC 66) 240) = true := by quickRfl

theorem kList : centList 12 6 95040 M12.T (M12A.T 0) 240 M12C.X M12C.P = true := by quickRfl

theorem kWit : conjWitK 12 6 95040 M12.T 240 M12C.P (M12A.T 0) 396 M12A.T M12C.H = true := by
  quickRfl

end CertificateChecks.KernelHSStd.M12K

end
