module

public import Certificates.Kernel.HN1408.RecGen
public import Certificates.Kernel.Sporadic.OddCore.MulHFamCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourCheck
import Certificates.Kernel.Sporadic.OrbRecGen
meta import Certificates.Kernel.HN1408.RecGen
meta import Certificates.Kernel.Sporadic.OddCore.MulHFamCmd
meta import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TwoFourCheck

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TfGen

open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.RecGen CFSG.PSL3Four.Native

meta def gz : Array (Array Nat) := gensM classz₁.centGens
meta def gzI : Array (Array Nat) := gz.map invM
meta def roots : Array (Array Nat) := (recOf (gensM nWords3)).extract 1 16
meta def orbs : Array (Array (Array Nat)) :=
  roots.map fun x => (bfs (fun j t => conjTab 1408 gz[j]! gzI[j]! t) 2 x 100).tabs
meta def oG : Array (Array (Array Nat)) := roots.map fun _ => gz
meta def oGI : Array (Array (Array Nat)) := roots.map fun _ => gzI
meta def sG : Array (Array (Array Nat)) := orbs.map idsOf
meta def sR : Array (Array Nat) := roots.map fun _ => idM

end CFSG.KD.HN1408.TfGen

end

namespace CFSG.KD.HN1408.TfGen

open CFSG.KS.MulHFamGen

meta def oD := mulhFam 1408 11 oG oGI roots 100
meta def oT : Array Nat := treeIn oD `T
meta def oGt : Array Nat := treeIn oD `G
meta def oGIt : Array Nat := treeIn oD `GI
meta def oR : Array Nat := treeIn oD `R
meta def oPL : Array Nat := treeIn oD `PL
meta def oPOS : Array Nat := treeIn oD `POS
meta def oSRT : Array Nat := treeIn oD `SRT
meta def oSRI : Array Nat := treeIn oD `SRI
meta def oHS : Array Nat := treeIn oD `HS
meta def oHSI : Array Nat := treeIn oD `HSI
meta def oCnt : Array Nat := treeIn oD `cnt
meta def oK : Array Nat := treeIn oD `k
meta def oN : CFSG.KC.Eval.Step := natStep oD

meta def sD := mulhFam 1408 11 sG orbs sR 100
meta def sT : Array Nat := treeIn sD `T
meta def sGt : Array Nat := treeIn sD `G
meta def sGIt : Array Nat := treeIn sD `GI
meta def sRt : Array Nat := treeIn sD `R
meta def sPL : Array Nat := treeIn sD `PL
meta def sPOS : Array Nat := treeIn sD `POS
meta def sSRT : Array Nat := treeIn sD `SRT
meta def sSRI : Array Nat := treeIn sD `SRI
meta def sHS : Array Nat := treeIn sD `HS
meta def sHSI : Array Nat := treeIn sD `HSI
meta def sCnt : Array Nat := treeIn sD `cnt
meta def sK : Array Nat := treeIn sD `k
meta def sN : CFSG.KC.Eval.Step := natStep sD

end CFSG.KD.HN1408.TfGen

set_option maxRecDepth 400000

#kc_nattree CFSG.KD.HN1408.TfO.T CFSG.KD.HN1408.TfGen.oT
#kc_nattree CFSG.KD.HN1408.TfO.G CFSG.KD.HN1408.TfGen.oGt
#kc_nattree CFSG.KD.HN1408.TfO.GI CFSG.KD.HN1408.TfGen.oGIt
#kc_nattree CFSG.KD.HN1408.TfO.R CFSG.KD.HN1408.TfGen.oR
#kc_nattree CFSG.KD.HN1408.TfO.PL CFSG.KD.HN1408.TfGen.oPL
#kc_nattree CFSG.KD.HN1408.TfO.POS CFSG.KD.HN1408.TfGen.oPOS
#kc_nattree CFSG.KD.HN1408.TfO.SRT CFSG.KD.HN1408.TfGen.oSRT
#kc_nattree CFSG.KD.HN1408.TfO.SRI CFSG.KD.HN1408.TfGen.oSRI
#kc_nattree CFSG.KD.HN1408.TfO.HS CFSG.KD.HN1408.TfGen.oHS
#kc_nattree CFSG.KD.HN1408.TfO.HSI CFSG.KD.HN1408.TfGen.oHSI
#kc_nattree CFSG.KD.HN1408.TfO.cnt CFSG.KD.HN1408.TfGen.oCnt
#kc_nattree CFSG.KD.HN1408.TfO.k CFSG.KD.HN1408.TfGen.oK
#kc_eval CFSG.KD.HN1408 TfO CFSG.KD.HN1408.TfGen.oN
#kc_nattree CFSG.KD.HN1408.TfS.T CFSG.KD.HN1408.TfGen.sT
#kc_nattree CFSG.KD.HN1408.TfS.G CFSG.KD.HN1408.TfGen.sGt
#kc_nattree CFSG.KD.HN1408.TfS.GI CFSG.KD.HN1408.TfGen.sGIt
#kc_nattree CFSG.KD.HN1408.TfS.R CFSG.KD.HN1408.TfGen.sRt
#kc_nattree CFSG.KD.HN1408.TfS.PL CFSG.KD.HN1408.TfGen.sPL
#kc_nattree CFSG.KD.HN1408.TfS.POS CFSG.KD.HN1408.TfGen.sPOS
#kc_nattree CFSG.KD.HN1408.TfS.SRT CFSG.KD.HN1408.TfGen.sSRT
#kc_nattree CFSG.KD.HN1408.TfS.SRI CFSG.KD.HN1408.TfGen.sSRI
#kc_nattree CFSG.KD.HN1408.TfS.HS CFSG.KD.HN1408.TfGen.sHS
#kc_nattree CFSG.KD.HN1408.TfS.HSI CFSG.KD.HN1408.TfGen.sHSI
#kc_nattree CFSG.KD.HN1408.TfS.cnt CFSG.KD.HN1408.TfGen.sCnt
#kc_nattree CFSG.KD.HN1408.TfS.k CFSG.KD.HN1408.TfGen.sK
#kc_eval CFSG.KD.HN1408 TfS CFSG.KD.HN1408.TfGen.sN
