module

public import Certificates.Kernel.Sporadic.Fi22.F3152Data
public import Certificates.Kernel.Fi22Core.Data
public import Certificates.Data.Kernel.Spor.F3LaneSep
public import CFSG.Certificates.Kernel.Spor.F3R
public import CFSG.Monster.B.Fischer.Fi22SepData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3152

open CFSG.F3.Native CFSG.KS.F3L CFSG.Monster.B.Fischer

@[expose] noncomputable def SepL : List V :=
  [SL 0, SL 1, SL 2, SL 3, SL 4, SL 10].map (CFSG.KS.F3152.mulK (SL 3511))

@[expose] noncomputable def SepW : V :=
  combL 77 (spreadE 77 77) CertificateChecks.KernelFi22C.LI SepL fi22SepTerms

@[expose] noncomputable def SepS : Array V := spinL 77 (SepL.map (trLane 77)) fi22SepVec fi22SepTree

set_option Elab.async false

theorem sep_wf : (SepW.wf && SepL.all V.wf) = true := by decide +kernel

theorem sep_zero : (mulVecL 77 (trLane 77 SepW) fi22SepVec).isZero = true := by decide +kernel

theorem sep_proj : CFSG.KS.F3R.eqMK 77 (CFSG.KS.F3R.mulK 77 fi22SepP (unlane 77 SepW))
    (projM 77 fi22SepVec fi22SepK) = true := by decide +kernel

theorem sep_spin : (SepS.size == 77 &&
    CFSG.KS.F3R.eqMK 77 (CFSG.KS.F3R.mulK 77 fi22SepTinv SepS) (idM 77)) = true := by
  decide +kernel

theorem sep_small : (decide (fi22SepK < 77) && fi22SepVec.canon 77 && fi22SepVec.get fi22SepK == 1 &&
    CFSG.KS.F3R.wfMK fi22SepP && CFSG.KS.F3R.wfMK fi22SepTinv && fi22SepP.size == 77 &&
    fi22SepTinv.size == 77 && fi22SepTerms.all (fun t => t.2.all (· < 6)) &&
    fi22SepTree.all (fun t => t.2 < 6) &&
    (List.range fi22SepTree.length).all (fun i => fi22SepTree[i]!.1 ≤ i)) = true := by
  decide +kernel

end CertificateChecks.KernelSpor.F3152

end
