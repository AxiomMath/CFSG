module

public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.LocalQT.PEnumFamD
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.LocalQT.PEnumFamD
meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.McLInvData

namespace CertificateChecks.KernelSpor.M27214

open CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.McLInv CFSG.Sporadic.McL.Native

meta def gRoM : Array (Array Nat) := gensR (orbitData ())
meta def gRiM : Array (Array Nat) := (gensR (orbitData ())).map (invTab 275)
meta def repsM : Array (Array Nat) := repsOf (enumBFS 275 (gensR (orbitData ())) 729)

meta def tWM : Array Nat :=
  let gJ := gensJ (orbitData ())
  let I := (orbitBFS 275 gJ (gJ.map (invTab 275)) gJ[0]! 22275).tabs
  let idx := indexOf I
  (enumBFS 275 (gensT (orbitData ())) 128).tabs.map fun t => idx.getD t 0

meta def rWM : Array Nat :=
  let os := repsM.map fun r => (orbitBFS 275 gRoM gRiM r 27).tabs
  let idxs := os.map indexOf
  (enumBFS 275 (gensR (orbitData ())) 729).tabs.map fun t =>
    let o := ((List.range os.size).find? fun o => (idxs[o]!).contains t).getD 0
    4096 * o + (idxs[o]!).getD t 0

meta def oD := CFSG.KS.PEnumFamDGen.penumFamD 275 9 true gRoM gRiM repsM 27

meta def oT : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `T
meta def oTO : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `TO
meta def oPL : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `PL
meta def oPLO : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `PLO
meta def oPOS : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `POS
meta def oPOSO : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `POSO
meta def oSRT : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `SRT
meta def oSRTO : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `SRTO
meta def oSRI : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `SRI
meta def oSRIO : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `SRIO
meta def oC : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `C
meta def oR : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `R
meta def oG : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `G
meta def oGI : Array Nat := CFSG.KS.PEnumFamDGen.treeIn oD `GI

meta def oN : CFSG.KC.Eval.Step := CFSG.KS.PEnumFamDGen.natStep oD

end CertificateChecks.KernelSpor.M27214

public section

set_option maxRecDepth 400000

#kc_nattree CertificateChecks.KernelSpor.MLO.T CertificateChecks.KernelSpor.M27214.oT
#kc_nattree CertificateChecks.KernelSpor.MLO.TO CertificateChecks.KernelSpor.M27214.oTO
#kc_nattree CertificateChecks.KernelSpor.MLO.PL CertificateChecks.KernelSpor.M27214.oPL
#kc_nattree CertificateChecks.KernelSpor.MLO.PLO CertificateChecks.KernelSpor.M27214.oPLO
#kc_nattree CertificateChecks.KernelSpor.MLO.POS CertificateChecks.KernelSpor.M27214.oPOS
#kc_nattree CertificateChecks.KernelSpor.MLO.POSO CertificateChecks.KernelSpor.M27214.oPOSO
#kc_nattree CertificateChecks.KernelSpor.MLO.SRT CertificateChecks.KernelSpor.M27214.oSRT
#kc_nattree CertificateChecks.KernelSpor.MLO.SRTO CertificateChecks.KernelSpor.M27214.oSRTO
#kc_nattree CertificateChecks.KernelSpor.MLO.SRI CertificateChecks.KernelSpor.M27214.oSRI
#kc_nattree CertificateChecks.KernelSpor.MLO.SRIO CertificateChecks.KernelSpor.M27214.oSRIO
#kc_nattree CertificateChecks.KernelSpor.MLO.C CertificateChecks.KernelSpor.M27214.oC
#kc_nattree CertificateChecks.KernelSpor.MLO.R CertificateChecks.KernelSpor.M27214.oR
#kc_nattree CertificateChecks.KernelSpor.MLO.G CertificateChecks.KernelSpor.M27214.oG
#kc_nattree CertificateChecks.KernelSpor.MLO.GI CertificateChecks.KernelSpor.M27214.oGI
#kc_eval CertificateChecks.KernelSpor MLO CertificateChecks.KernelSpor.M27214.oN

#krows32 CertificateChecks.KernelSpor.MLTW CertificateChecks.KernelSpor.M27214.tWM

#krows32 CertificateChecks.KernelSpor.MLRW CertificateChecks.KernelSpor.M27214.rWM

end
