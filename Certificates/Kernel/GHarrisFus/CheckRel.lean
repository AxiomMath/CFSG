module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataA
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataB
public import Certificates.Data.Kernel.GHarrisFus.RelDefs
public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import all Init.Data.List.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus CFSG.KD.GHFus

theorem ch22608rel_aZ : relB Fus.aZ aZ = true := by quickRfl
theorem ch22608rel_aT : relB Fus.aT aT = true := by quickRfl
theorem ch22608rel_aA1L : relB Fus.aA1L aA1L = true := by quickRfl
theorem ch22608rel_aA34 : relB Fus.aA34 aA34 = true := by quickRfl
theorem ch22609rel_yIZ : relB Fus.yIZ yIZ = true := by quickRfl
theorem ch22609rel_yIX : relB Fus.yIX yIX = true := by quickRfl
theorem ch22609rel_bIZ : relB Fus.bIZ bIZ = true := by quickRfl
theorem ch22609rel_bIA1L : relB Fus.bIA1L bIA1L = true := by quickRfl
theorem ch22609rel_bIX : relB Fus.bIX bIX = true := by quickRfl
theorem ch22609rel_bIIZ : relB Fus.bIIZ bIIZ = true := by quickRfl
theorem ch22609rel_bIIA1L : relB Fus.bIIA1L bIIA1L = true := by quickRfl
theorem ch22609rel_bIIX : relB Fus.bIIX bIIX = true := by quickRfl
theorem ch22609rel_bIIA34 : relB Fus.bIIA34 bIIA34 = true := by quickRfl
theorem ch22609rel_yIIZ : relB Fus.yIIZ yIIZ = true := by quickRfl
theorem ch22609rel_yIIA34 : relB Fus.yIIA34 yIIA34 = true := by quickRfl
theorem ch22609rel_yIIX : relB Fus.yIIX yIIX = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
