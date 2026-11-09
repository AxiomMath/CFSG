module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Sporadic.Schreier.RuDefs
meta import CFSG.Sporadic.Schreier.RuDefs
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Perm.HexTabCmd
public import CFSG.Certificates.Kernel.SporSch.RuTextSplit
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.Schreier.RuEnum
public import Mathlib.GroupTheory.Schreier
meta import CFSG.Sporadic.Schreier.RuEnum
meta import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuT4060 CFSG.Sporadic.RuSchreier.ru4060Text

#ks_hexlines_tab CertificateChecks.KernelSporSch.RuT4060 CFSG.Sporadic.RuSchreier.ru4060Text 3 4060 12

namespace CertificateChecks.KernelSporSch.RuT4060

open CFSG.KS.Text CFSG.KC.Misc.HexFlat

theorem p0 :
    hexBind (takeL 60905 (dropL 0 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 0)) =
      true := by quickRfl
theorem p1 :
    hexBind (takeL 60905 (dropL 60905 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 1)) =
      true := by quickRfl
theorem p2 :
    hexBind (takeL 60905 (dropL 121810 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 2)) =
      true := by quickRfl
theorem p3 :
    hexBind (takeL 60905 (dropL 182715 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 3)) =
      true := by quickRfl
theorem p4 :
    hexBind (takeL 60905 (dropL 243620 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 4)) =
      true := by quickRfl
theorem p5 :
    hexBind (takeL 60905 (dropL 304525 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 5)) =
      true := by quickRfl
theorem p6 :
    hexBind (takeL 60905 (dropL 365430 (dropL 0 chars))) 3 4060 12 5 0 5 (shF L (5 * 6)) =
      true := by quickRfl
theorem p7 :
    hexBind (takeL 60905 (dropL 26336 (dropL 399999 chars))) 3 4060 12 5 0 5 (shF L (5 * 7)) =
      true := by quickRfl
theorem p8 :
    hexBind (dropL 87241 (dropL 399999 chars)) 3 4060 12 5 0 5 (shF L (5 * 8)) = true := by
  quickRfl

theorem all : hexBind chars (nat_lit 3) (nat_lit 4060) (nat_lit 12) (nat_lit 45) (nat_lit 0)
    (nat_lit 45) L = true :=
  hexBind_of_sufR (by decide) <|
    sufR_step p0 (by decide) (by decide) (by decide)
    (sufR_step p1 (by decide) (by decide) (by decide)
    (sufR_step p2 (by decide) (by decide) (by decide)
    (sufR_step p3 (by decide) (by decide) (by decide)
    (sufR_step p4 (by decide) (by decide) (by decide)
    (sufR_step p5 (by decide) (by decide) (by decide)
    (sufR_step p6 (by decide) (by decide) (by decide)
    (sufR_step p7 (by decide) (by decide) (by decide)
    (sufR_last p8 (by decide)))))))))

end CertificateChecks.KernelSporSch.RuT4060

end
