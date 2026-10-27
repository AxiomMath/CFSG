module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.LocalComp.HeFix2329.Data
public import Certificates.Kernel.LocalComp.HeFix2329.Enum
public import Certificates.Kernel.LocalComp.HeAutEnum
public import Certificates.Data.Kernel.HeFixK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeFix2329

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermTool CFSG.KC.HexaK
open CFSG.KC.HeFixK CFSG.ComponentClassification.GrSLit.HeldFix
open CertificateChecks.KernelLC CertificateChecks.KernelLC.HeFix

theorem kGT : (Nat.beq HeT32.ng 5 && allN 5 fun k => Nat.beq (HeT32.G k) (Q k)) = true := by
  quickRfl

theorem kGE : (Nat.beq HeE32.ng 6 &&
    allN 6 fun i => Nat.beq (HeE32.G i) (wordTabK 32 6 Q (hfEWords.getD i []))) = true := by
  quickRfl

theorem kPerm32 :
    (allN HeT32.ng (fun k => permOK 32 6 (mask 6) (32 * 6) (HeT32.G k) (pinvS 32 6 (mask 6) (HeT32.G k))) &&
      allN HeE32.ng fun k => permOK 32 6 (mask 6) (32 * 6) (HeE32.G k) (pinvS 32 6 (mask 6) (HeE32.G k))) =
      true := by
  quickRfl

theorem kId32 : (canonK 32 6 (mask 6) (32 * 6) (pidn 32 6) && idK 32 6 (mask 6)) = true := by
  quickRfl

theorem kCen : Nat.beq (cenK HeT32.N HeT32.T HeT32.ng HeT32.G) 2 = true := by quickRfl

theorem kE : eK HeE32.ng HeE32.G = true := by quickRfl

theorem kNorm : normK HeT32.ng HeT32.G HeE32.N HeE32.T HeE32.ng HeE32.G = true := by quickRfl

theorem kIT : itK HeT32.N HeT32.T IT = true := by quickRfl

theorem kOuter : Nat.beq (outerK HeAutY.N HeAutY.T HeT32.N HeT32.T IT WT) 769 = true := by quickRfl

end CertificateChecks.KernelLC.HeFix2329

end
