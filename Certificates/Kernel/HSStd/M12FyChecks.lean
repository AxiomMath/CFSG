module

public import Certificates.Kernel.HSStd.M12FyData
public import Certificates.Data.Kernel.L34Cover
public import Certificates.Data.Kernel.GrpWitK
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelHSStd.M12Fy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Inv CFSG.KC.GrpWit
open CFSG.EvenSporadicStandard.HSStd.FiveY
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def QT (o j : Nat) : Nat := nIf(Nat.beq o (nat_lit 0), Q0.T j, Q1.T j)

@[expose] noncomputable def QN (o : Nat) : Nat := nIf(Nat.beq o (nat_lit 0), Q0.N, Q1.N)

@[expose] noncomputable def cv (s : Nat) : Bool := covSl 12 6 M.T QT QN 2 W 1440 s

@[expose] noncomputable def cm (r : Nat) : Bool := commK 12 6 (Nat.mul 30 r) 30 C.N C.T D.N D.T 6 CW

end CertificateChecks.KernelHSStd.M12Fy

#kon_slices CertificateChecks.KernelHSStd.M12Fy.cv 0 66
#kon_join CertificateChecks.KernelHSStd.M12Fy.cvAll CertificateChecks.KernelHSStd.M12Fy.cv 66
#kon_slices CertificateChecks.KernelHSStd.M12Fy.cm 0 8
#kon_join CertificateChecks.KernelHSStd.M12Fy.cmAll CertificateChecks.KernelHSStd.M12Fy.cm 8

namespace CertificateChecks.KernelHSStd.M12Fy

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34Inv CFSG.KC.GrpWit
open CFSG.EvenSporadicStandard.HSStd.FiveY
open CFSG.KLie.CT (fget andB orB notB)

theorem kBind : (Nat.beq m12Gens.size 2 && allN 2 (fun k => bindArrK m12Gens[k]! 12 6 (M.G k)) &&
    Nat.beq m12CGens.size 4 && allN 4 (fun k => bindArrK m12CGens[k]! 12 6 (C.G k)) &&
    Nat.beq m12DGens.size 2 && allN 2 (fun k => bindArrK m12DGens[k]! 12 6 (D.G k)) &&
    bindArrK m12Inv0 12 6 (Q0.T Q0.r0) && bindArrK m12Inv1 12 6 (Q1.T Q1.r0) &&
    Nat.beq Q0.ng 2 && Nat.beq Q1.ng 2 && Nat.beq M.ng 2 && Nat.beq C.ng 4 && Nat.beq D.ng 2 &&
    Nat.beq M.N 95040 && Nat.beq C.N 240 && Nat.beq D.N 60 && Nat.beq Q0.N 396 &&
    Nat.beq Q1.N 495 && Nat.blt Q0.r0 Q0.N && Nat.blt Q1.r0 Q1.N &&
    Nat.beq (M.T 0) (pidn 12 6) && Nat.beq (C.T 0) (pidn 12 6) && Nat.beq (D.T 0) (pidn 12 6) &&
    allN 2 (fun k => Nat.beq (Q0.G k) (M.G k) && Nat.beq (Q1.G k) (M.G k))) = true := by
  quickRfl

theorem kInv : (Nat.beq (pcomp 12 6 (mask 6) (Q0.T Q0.r0) (Q0.T Q0.r0)) (pidn 12 6) &&
    !Nat.beq (Q0.T Q0.r0) (pidn 12 6) &&
    Nat.beq (pcomp 12 6 (mask 6) (Q1.T Q1.r0) (Q1.T Q1.r0)) (pidn 12 6) &&
    !Nat.beq (Q1.T Q1.r0) (pidn 12 6)) = true := by quickRfl

theorem kPerms : (permsK 12 6 240 C.T && permsK 12 6 60 D.T && permsK 12 6 396 Q0.T &&
    permsK 12 6 495 Q1.T) = true := by
  quickRfl

theorem kCent : centMemK 12 6 (Q0.T Q0.r0) 4 C.G 95040 M.T CM = true := by quickRfl

theorem kInvD : invWitK 12 6 (pidn 12 6) (Q0.T Q0.r0) 60 D.T 396 Q0.T DW = true := by quickRfl

end CertificateChecks.KernelHSStd.M12Fy

end
