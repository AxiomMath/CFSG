module

public import Certificates.Kernel.LocalQT.PEnumD
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterData

namespace CertificateChecks.KernelSpor.S27215

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.SuzOuter

meta def idM : Array Nat := idTab 1782
meta def gCM : Array (Array Nat) := gensC
meta def gIM : Array (Array Nat) := gensC.map (invTab 1782)
meta def gPM : Array (Array Nat) := gensP
meta def rAM : Array Nat := repTab 0
meta def rBM : Array Nat := repTab 1
meta def rCM : Array Nat := repTab 2
meta def eGM : Array (Array Nat) := gensE (orbitBFS 1782 gensC gIM (repTab 0) 315)

meta def coverM : Array Nat :=
  let os := #[(orbitBFS 1782 gensC gIM (repTab 0) 315).tabs,
    (orbitBFS 1782 gensC gIM (repTab 1) 2520).tabs, (orbitBFS 1782 gensC gIM (repTab 2) 1800).tabs]
  let idxs := os.map indexOf
  (enumBFS 1782 gensP 256).tabs.map fun t =>
    let o := ((List.range 3).find? fun o => (idxs[o]!).contains t).getD 0
    4096 * o + (idxs[o]!).getD t 0

end CertificateChecks.KernelSpor.S27215

public section

set_option maxRecDepth 400000

#kpenum_d CertificateChecks.KernelSpor.SOP 1782 11 false CertificateChecks.KernelSpor.S27215.gPM
  CertificateChecks.KernelSpor.S27215.gPM CertificateChecks.KernelSpor.S27215.idM 256

#kpenum_d CertificateChecks.KernelSpor.SOA 1782 11 true CertificateChecks.KernelSpor.S27215.gCM
  CertificateChecks.KernelSpor.S27215.gIM CertificateChecks.KernelSpor.S27215.rAM 315

#kpenum_d CertificateChecks.KernelSpor.SOB 1782 11 true CertificateChecks.KernelSpor.S27215.gCM
  CertificateChecks.KernelSpor.S27215.gIM CertificateChecks.KernelSpor.S27215.rBM 2520

#kpenum_d CertificateChecks.KernelSpor.SOC 1782 11 true CertificateChecks.KernelSpor.S27215.gCM
  CertificateChecks.KernelSpor.S27215.gIM CertificateChecks.KernelSpor.S27215.rCM 1800

#kpenum_d CertificateChecks.KernelSpor.SOE 1782 11 false CertificateChecks.KernelSpor.S27215.eGM
  CertificateChecks.KernelSpor.S27215.eGM CertificateChecks.KernelSpor.S27215.idM 128

#krows32 CertificateChecks.KernelSpor.SOW CertificateChecks.KernelSpor.S27215.coverM

end
