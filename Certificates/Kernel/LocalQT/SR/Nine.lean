module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineSporadicInputs
public import CFSG.Open.Defs
import CFSG.Adapters.ProjectiveSpecialLinear
meta import CFSG.CGT.Timmesfeld75.L2Pair
meta import CFSG.CGT.Timmesfeld75.ListWCBasic
meta import CFSG.ClassicalGroups
meta import CFSG.LieType.BorelTits.CompleteFlag
meta import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
meta import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
meta import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
meta import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
meta import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
meta import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
meta import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
meta import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
meta import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineBasic
meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
meta import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
meta import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
meta import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
meta import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
meta import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.J2N CFSG.QuasithinUnique.Id2519.j2NineData 5 14
  CFSG.Blueprint.NativeSporadic.J2Seed1 CFSG.Blueprint.NativeSporadic.J2Seed2

#lqt_sr_elem CFSG.KD.LQT.HSN CFSG.QuasithinUnique.Id2519.hsNineData 2 20
  CFSG.Blueprint.NativeSporadic.HSSeed1 CFSG.Blueprint.NativeSporadic.HSSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem j2_nine : ∃ E : Subgroup NativeSporadic.J2, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have h := elem_sound _ CFSG.KD.LQT.J2N.lay_ok CFSG.KD.LQT.J2N.decA CFSG.KD.LQT.J2N.decB
    CFSG.KD.LQT.J2N.one CFSG.KD.LQT.J2N.steps CFSG.KD.LQT.J2N.elem
  rw [← CFSG.KD.LQT.J2N.LA_eq, ← CFSG.KD.LQT.J2N.LB_eq] at h
  exact h

theorem hs_nine : ∃ E : Subgroup NativeSporadic.HS, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  have h := elem_sound _ CFSG.KD.LQT.HSN.lay_ok CFSG.KD.LQT.HSN.decA CFSG.KD.LQT.HSN.decB
    CFSG.KD.LQT.HSN.one CFSG.KD.LQT.HSN.steps CFSG.KD.LQT.HSN.elem
  rw [← CFSG.KD.LQT.HSN.LA_eq, ← CFSG.KD.LQT.HSN.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
