module

public import Certificates.Data.Kernel.GapsK
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Data
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataA7
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataA8
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataA9
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.DataMathieu
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGapsK

open CFSG.KC.GapsK CFSG.KC.S97RYK CFSG.CGT.Timmesfeld75.WCCheck CFSG.Sporadic.Th.Native
open CFSG.RankThree.GF2n.Tim81.Gaps

theorem a6_base : gapsBaseK a6GData.D = true := by quickRfl

theorem a7_base : gapsBaseK a7GData.D = true := by quickRfl

theorem a8_base : gapsBaseK a8GData.D = true := by quickRfl

theorem a9_base : gapsBaseK a9GData.D = true := by quickRfl

theorem a6_ok : gapsVerdictsK a6GData = true := by quickRfl

theorem a7_ok : gapsVerdictsK a7GData = true := by quickRfl

theorem a8_ok : gapsVerdictsK a8GData = true := by quickRfl

theorem a9_ok : gapsVerdictsK a9GData = true := by quickRfl

theorem m22_ok : gapsVerdictsK m22GData = true := by quickRfl

theorem m23_ok : gapsVerdictsK m23GData = true := by quickRfl

theorem m24_ok : gapsVerdictsK m24GData = true := by quickRfl

theorem a6_gens : [a6tA, a6tAi, a6tB, a6tBi, idT 6].all (validT 6) = true := by quickRfl

theorem a7_gens : [a7tA, a7tAi, a7tB, a7tBi, idT 7].all (validT 7) = true := by quickRfl

theorem a8_gens : [a8tA, a8tAi, a8tB, a8tBi, idT 8].all (validT 8) = true := by quickRfl

theorem a9_gens : [a9tA, a9tAi, a9tB, a9tBi, idT 9].all (validT 9) = true := by quickRfl

end CertificateChecks.KernelGapsK

end
