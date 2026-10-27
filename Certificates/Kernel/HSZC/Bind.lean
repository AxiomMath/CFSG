module

public import Certificates.Kernel.HSZC.Data
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCHSVDefs

public section

namespace CertificateChecks.HSZCK

open CFSG.KD.HSZC CFSG.KS.Raw.Orb CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem a_prep : PRep 100 7 A hsVa := by unfold PRep; decide +kernel
theorem ai_prep : PRep 100 7 AI hsVa⁻¹ := by unfold PRep; decide +kernel
theorem b_prep : PRep 100 7 B hsVb := by unfold PRep; decide +kernel
theorem bi_prep : PRep 100 7 BI hsVb⁻¹ := by unfold PRep; decide +kernel

end CertificateChecks.HSZCK

end
