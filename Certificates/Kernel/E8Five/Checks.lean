module

public import Certificates.Data.Kernel.E8Five.Defs
public import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelE8Five

open CFSG.KC.E8Five CFSG.Blueprint.Chevalley

set_option maxRecDepth 100000

theorem ch14974kM2 : maskOK (rowsOfK mEig2 Tag.E8.artifactRoots) mask2 = true := by
  decide +kernel

theorem ch14974kM3 : maskOK (rowsOfK mEig3 Tag.E8.artifactRoots) mask3 = true := by
  decide +kernel

#kc_each CertificateChecks.KernelE8Five ch14974kH2 (fun j => hypOKFrom mask2 (125 * j) 125) 0 5

#kc_each CertificateChecks.KernelE8Five ch14974kH3 (fun j => hypOKFrom mask3 (125 * j) 125) 0 5

theorem ch14975kF1 : fixOK (rowsOfK mFix1 Tag.E8.artifactRoots) = true := by decide +kernel

theorem ch14975kF2 : fixOK (rowsOfK mFix2 Tag.E8.artifactRoots) = true := by decide +kernel

theorem ch14974k_negMask : maskOK (rowsOfK mEig2 Tag.E8.artifactRoots) mask3 = false := by
  decide +kernel

theorem ch14974k_negHyp : hypOKFrom 0 0 125 = false := by decide +kernel

theorem ch14975k_negFix : fixOK (rowsOfK mEig2 Tag.E8.artifactRoots) = false := by
  decide +kernel

end CertificateChecks.KernelE8Five
