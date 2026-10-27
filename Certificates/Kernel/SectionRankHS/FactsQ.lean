module

public import Certificates.Kernel.SectionRankHS.Seeds
public import Certificates.Kernel.SectionRankHS.RuSeeds
public import Certificates.Data.Kernel.OpsF2KMcertQ
public import CFSG.RankThree.Asc83Table.HSData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2HSInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporHS5Inputs

public section

namespace CertificateChecks.KernelSRHS

open CFSG.KC.OpsF2K CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.Asc83Table.HS CFSG.RankThree.PartOne.CTP.Fus
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native

theorem mcert_Q : mcertQ 20 SA.M SB.M hsCert = true := by decide +kernel

theorem fusD2_Q : fusQ 20 SA.M SB.M fusD2HSN fusD2HSProg fusD2HS = true := by decide +kernel

theorem fusFive_Q : fusQ 20 SA.M SB.M fusHSFiveN fusHSFiveProg fusHSFive = true := by
  decide +kernel

theorem e8HS_Q : e8Q 20 SA.M SB.M hsE8Data = true := by decide +kernel

theorem e8Ru_Q : e8Q 28 RA.M RB.M ruE8Data = true := by decide +kernel

theorem mcert_negQ : (!mcertQ 20 SA.M SB.M { hsCert with facts := [MFact.ord 7 3] }) = true := by
  decide +kernel

theorem mcert_neg_eqQ :
    (!mcertQ 20 SA.M SB.M { hsCert with facts := [MFact.eq [(5, 1)] [(6, 1)]] }) = true := by
  decide +kernel

theorem fus_negQ : (!fusQ 20 SA.M SB.M fusD2HSN fusD2HSProg { fusD2HS with rA := 1 }) = true := by
  decide +kernel

theorem e8_negQ : (!e8Q 20 SB.M SA.M hsE8Data) = true := by decide +kernel

end CertificateChecks.KernelSRHS
