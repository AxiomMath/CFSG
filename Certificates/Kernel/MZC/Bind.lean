module

public import Certificates.Kernel.MZC.Data
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCData
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermData

public section

namespace CertificateChecks.MZCK

open CFSG.KS.Raw.Orb CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem a225 : PRep 22 5 CFSG.KD.M225.A PermGens.m22a := by unfold PRep; decide +kernel
theorem ai225 : PRep 22 5 CFSG.KD.M225.AI PermGens.m22a⁻¹ := by unfold PRep; decide +kernel
theorem b225 : PRep 22 5 CFSG.KD.M225.B PermGens.m22b := by unfold PRep; decide +kernel
theorem bi225 : PRep 22 5 CFSG.KD.M225.BI PermGens.m22b⁻¹ := by unfold PRep; decide +kernel
theorem a227 : PRep 22 5 CFSG.KD.M227.A PermGens.m22a := by unfold PRep; decide +kernel
theorem ai227 : PRep 22 5 CFSG.KD.M227.AI PermGens.m22a⁻¹ := by unfold PRep; decide +kernel
theorem b227 : PRep 22 5 CFSG.KD.M227.B PermGens.m22b := by unfold PRep; decide +kernel
theorem bi227 : PRep 22 5 CFSG.KD.M227.BI PermGens.m22b⁻¹ := by unfold PRep; decide +kernel
theorem a235 : PRep 23 5 CFSG.KD.M235.A PermGens.m23a := by unfold PRep; decide +kernel
theorem ai235 : PRep 23 5 CFSG.KD.M235.AI PermGens.m23a⁻¹ := by unfold PRep; decide +kernel
theorem b235 : PRep 23 5 CFSG.KD.M235.B PermGens.m23b := by unfold PRep; decide +kernel
theorem bi235 : PRep 23 5 CFSG.KD.M235.BI PermGens.m23b⁻¹ := by unfold PRep; decide +kernel

end CertificateChecks.MZCK

end
