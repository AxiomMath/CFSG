module

public import Certificates.Kernel.MaxD2.HSW0.Data
public import Certificates.Kernel.MaxD2.HSP.Enum
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Kernel.MaxD2.HSU.Enum
public import Certificates.Kernel.MaxD2.HSOver.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.HSOverData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSW0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSOver

@[expose] noncomputable def xK : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (PW 0) (PW 2)) (PW 1)

@[expose] noncomputable def w0K : Bool :=
  wordEqK 100 7 (mask 7) (pidn 100 7) HSOver.GP HSOver.GPI 3 hsOverW0W (PW 0) &&
  (permOK 100 7 (mask 7) (100 * 7) (PW 0) (PW 1) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverGAW (PW 2) &&
  (canonK 100 7 (mask 7) (100 * 7) (PW 2) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsOverGBW (PW 3) &&
  (permOK 100 7 (mask 7) (100 * 7) (PW 3) (PW 4) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.uW (HSU.RE.G 0) &&
  (wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2 hsFiveDataP.vW (HSU.RE.G 1) &&
  (allN 2 (fun i => conjInK 100 7 HSU.RE.cnt HSU.RE.T (PW 0) (PW 1) (HSU.RE.G i) (r32 HW i)) &&
  (notInK HSP.NE.cnt HSP.NE.T (PW 0) &&
  (allN 4 (fun j => conjInK 100 7 HSP.NE.cnt HSP.NE.T (PW 0) (PW 1) (HSP.NE.G j)
    (r32 HW (Nat.add 2 j))) &&
  (Nat.blt (r32 HW 6) HSP.NE.cnt &&
  conjInK 100 7 HSP.NE.cnt HSP.NE.T (PW 4) xK (HSP.NE.T (r32 HW 6)) (r32 HW 7))))))))))))

theorem k_w0 : w0K = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSW0

end
