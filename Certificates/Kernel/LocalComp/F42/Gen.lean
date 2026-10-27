module

public import Certificates.Kernel.LocalComp.F42.Misc
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.EvenSmallLie.FFourTwo

theorem gen_L : genOK (2 ^ 23) wordsL = true := by
  delta genOK letterOK witProd commHU hOK hU conjU negU mulU invU Pc.mul Pc.mulList
  simp only [mg_eq, mw_eq, inv_eq]
  quickRfl

theorem gen_Lt : genOK (2 ^ 23 + 2 ^ 24) wordsL = true := by
  delta genOK letterOK witProd commHU hOK hU conjU negU mulU invU Pc.mul Pc.mulList
  simp only [mg_eq, mw_eq, inv_eq]
  quickRfl

theorem gen_S : genOK (2 ^ 22) wordsS = true := by
  delta genOK letterOK witProd commHU hOK hU conjU negU mulU invU Pc.mul Pc.mulList
  simp only [mg_eq, mw_eq, inv_eq]
  quickRfl

theorem gen_St : genOK (2 ^ 22 + 2 ^ 24) wordsS = true := by
  delta genOK letterOK witProd commHU hOK hU conjU negU mulU invU Pc.mul Pc.mulList
  simp only [mg_eq, mw_eq, inv_eq]
  quickRfl

theorem gen_okAll : genCheck = true := by
  simp only [genCheck, gen_L, gen_Lt, gen_S, gen_St, Bool.and_self]

end CertificateChecks.KernelLC.F42

end
