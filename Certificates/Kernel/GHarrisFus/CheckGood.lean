module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataA
public import Certificates.Data.Kernel.GHarrisFus.GoodDefs
public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import all Init.Data.List.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus CFSG.KD.GHFus

theorem ch22608ikAZ : ikB Fus.aZBase aZ.2.2.2.1 = true := by quickRfl
theorem ch22608ikA34 : ikB Fus.aA34Base aA34.2.2.2.1 = true := by quickRfl
theorem ch22608xAZ : wordsB Fus.aZBase [26, 4, 2] [aZx.1, aZx.2.1, aZx.2.2] = true := by quickRfl
theorem ch22608xA34 :
    wordsB Fus.aA34Base [26, 2, 3, 4] [aA34x.1, aA34x.2.1, aA34x.2.2.1, aA34x.2.2.2] = true := by
  quickRfl
theorem ch22608witAZ : codesB aZwit = true := by quickRfl
theorem ch22608witA34 : codesB aA34wit = true := by quickRfl
theorem ch22608a1 : (Fus.A1list.map SE.enc == a1K) = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
