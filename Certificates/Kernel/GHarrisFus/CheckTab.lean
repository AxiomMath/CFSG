module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataA
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusDataB
public import Certificates.Data.Kernel.GHarrisFus.Cls
public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Array.Basic
import all Init.Data.Range.Basic
import all Init.Data.List.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus

theorem ch22608tab_aZ : Fus.aZ.tableOk (· * ·) = true := by quickRfl
theorem ch22608tab_aT : Fus.aT.tableOk (· * ·) = true := by quickRfl
theorem ch22608tab_aA1L : Fus.aA1L.tableOk (· * ·) = true := by quickRfl
theorem ch22608tab_aA34 : Fus.aA34.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_yIZ : Fus.yIZ.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_yIX : Fus.yIX.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIZ : Fus.bIZ.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIA1L : Fus.bIA1L.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIX : Fus.bIX.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIIZ : Fus.bIIZ.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIIA1L : Fus.bIIA1L.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIIX : Fus.bIIX.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_bIIA34 : Fus.bIIA34.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_yIIZ : Fus.yIIZ.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_yIIA34 : Fus.yIIA34.tableOk (· * ·) = true := by quickRfl
theorem ch22609tab_yIIX : Fus.yIIX.tableOk (· * ·) = true := by quickRfl

theorem ch22608clsW : clsWOK CFSG.KD.GHFus.clsW = true := by quickRfl
theorem ch22608clsCover : clsCover CFSG.KD.GHFus.clsW = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
