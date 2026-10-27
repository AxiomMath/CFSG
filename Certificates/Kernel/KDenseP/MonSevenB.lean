module

public import Certificates.Kernel.KDenseP.MonSeven
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBData
public import CFSG.YGroups.Y443.Native.Words
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R17473
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWords
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R716100
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.R716201

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.MonSeven

open CFSG.KC.KDenseP.MonSeven CFSG.AGLEmbedding.Norton.MON5_7

set_option maxRecDepth 100000

theorem agreeAll_of_opEqs {qs : Prs} (h : OpEqs qs) : agreeAll qs = true :=
  agreeAll_of_wordLin (fun p hp => ⟨(h p hp).1, (h p hp).2.1⟩) fun p hp => (h p hp).2.2

theorem c17473 : agreeAll CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bT3Eqs = true :=
  agreeAll_of_opEqs (kd_m7% CFSG.KD.M7.c17473 CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bT3Eqs)

theorem c716100 :
    agreeAll CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag.m7hPairs = true :=
  agreeAll_of_opEqs (kd_m7% CFSG.KD.M7.c716100
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag.m7hPairs)

theorem c716201 :
    agreeAll CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive.m5tEqs = true :=
  agreeAll_of_opEqs (kd_m7% CFSG.KD.M7.c716201
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive.m5tEqs)

end CertificateChecks.KernelKDenseP.MonSeven

end
