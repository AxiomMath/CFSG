module

public import Certificates.Data.Kernel.SuzI301K
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Kernel.Sporadic.SuzI301K.Data
public import Certificates.Kernel.Sporadic.SuzH.Data
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Kernel.Sporadic.Suz.Text2306
public import Certificates.Kernel.Sporadic.SuzInv.Text1
public import Certificates.Kernel.LocalComp.B0SuzData
public import Certificates.Kernel.SuzPump.Pair
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.LinRep CFSG.KC.SuzI301K
open CertificateChecks.KernelLC CertificateChecks.KernelSuzPump

@[expose] noncomputable def TAU : Nat := pm Suz2306.V (SuzHS.F 4)

@[expose] noncomputable def XA : Nat := (reb CFSG.HardMathSupport.Dickson.I271.TabSuzFuse.xATuple).1

@[expose] noncomputable def siftS (G : Nat) : Bool :=
  siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G

@[expose] noncomputable def J (c i : Nat) : Nat := nthN CFSG.KD.SuzI301.QJ (Nat.add (Nat.mul 6 c) i)

theorem kPerm : (permB 1782 11 (SuzHS.F 0) && permB 1782 11 (SuzHS.F 1) &&
    permB 1782 11 (SuzHS.F 2) && permB 1782 11 (SuzHS.F 3) && permB 1782 11 (SuzHS.F 4) &&
    permB 1782 11 Suz2306.V && permB 1782 11 (SuzInvT1.F 0)) = true := by quickRfl

theorem kSiftH : siftS (SuzHS.F 0) = true := by quickRfl

theorem kSiftM : siftS (SuzHS.F 4) = true := by quickRfl

theorem kSiftB2 : siftS (SuzHS.F 2) = true := by quickRfl

theorem kSiftB3 : siftS (SuzHS.F 3) = true := by quickRfl

theorem kRel : relK (SuzHS.F 0) XA (SuzHS.F 1) (SuzHS.F 2) (SuzHS.F 3) (SuzInvT1.F 0) TAU = true := by
  quickRfl

theorem kCrdD : crdK (SuzHS.F 1) SuzB0Q.F SuzB0QE (J 0) = true := by quickRfl

theorem kCrdB2 : crdK (SuzHS.F 2) SuzB0Q.F SuzB0QE (J 1) = true := by quickRfl

theorem kCrdB3 : crdK (SuzHS.F 3) SuzB0Q.F SuzB0QE (J 2) = true := by quickRfl

theorem kCrdT : crdK TAU SuzB0Q.F SuzB0QE (J 3) = true := by quickRfl

theorem kFix : fixK (SuzHS.F 1) SuzB0QE (nthN CFSG.KD.SuzI301.CW 0) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzI301K

end
