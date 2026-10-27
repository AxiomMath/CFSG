module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Sporadic.OddCore.HL
public import Certificates.Kernel.LocalComp.L34RData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixIsoCheckInputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixIsoCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeldFixGraph

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.HeldFix

meta def gM : Array (Array Nat) := heldFixGraphGens

meta def idM : Array Nat := idTab 147

end CertificateChecks.KernelLC.HeldFixGraph

#kpenum CertificateChecks.KernelLC.HFG 147 8 false CertificateChecks.KernelLC.HeldFixGraph.gM
  CertificateChecks.KernelLC.HeldFixGraph.gM CertificateChecks.KernelLC.HeldFixGraph.idM 20160

namespace CertificateChecks.KernelLC.HeldFixGraph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def DD : Array Tab :=
  Array.ofFn (n := 5) fun j => unpack 105 7 (CertificateChecks.KernelSpor.HDE.G j.val)

@[expose] noncomputable def SS : Array Tab :=
  Array.ofFn (n := 3) fun j => unpack 42 6 (L34R.G j.val)

@[expose] noncomputable def hgg : Array Tab :=
  Array.ofFn (n := 8) fun k =>
    if k.val < 5 then
      catTab 105 42 DD[k.val]! (wordTabS 42 SS (heldFixSWords.getD k.val []))
    else
      catTab 105 42 (wordTabS 105 DD (heldFixXWords.getD (k.val - 5) [])) SS[k.val - 5]!

@[expose] noncomputable def ck (s : Nat) : Bool :=
  penumSlK 147 8 (mask 8) (147 * 8) false HFG.G HFG.GI 8 HFG.cnt HFG.T HFG.PL HFG.POS HFG.SRT
    HFG.SRI (Nat.mul s (nat_lit 32)) (nat_lit 32)

theorem k_gens : gensK hgg 147 8 8 HFG.G = true := by
  quickRfl

theorem k_hd : bAnd(Nat.beq HFG.k 8, bAnd(Nat.beq HFG.cnt 20160,
    penumHdK (pidn 147 8) HFG.cnt 20160 HFG.T HFG.PL)) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeldFixGraph

end
