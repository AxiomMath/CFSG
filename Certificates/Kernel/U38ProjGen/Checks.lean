module

public import Certificates.Data.Kernel.U38ProjGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38S1Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38P1Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Y9Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftU38Data

public section

set_option maxRecDepth 100000
set_option Elab.async false

namespace CertificateChecks.KernelU38PG

open CFSG.KC.U38PG CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.U38
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.Eight

theorem u38pg9588_check : projGenK s1Gen = true := by decide +kernel

theorem u38pg9589_check : projGenK p1Gen = true := by decide +kernel

theorem u38pg9670_check : projGenK y9Gen = true := by decide +kernel

theorem u38pg9690_check : projGenK z8Gen = true := by decide +kernel

end CertificateChecks.KernelU38PG
