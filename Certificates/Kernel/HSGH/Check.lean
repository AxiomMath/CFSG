module

public import Certificates.Data.Kernel.TabMatGrp
public import Certificates.Kernel.VecCert.HS
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCertCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSGH

open CFSG.KC.TabMatGrp CFSG.ComponentClassification.HSFLit.GHCert CertificateChecks.KernelVec.HS

@[expose] def segs : List (List (Fin 2 × Bool)) := abWords.map fun w => w.map pairLetter

@[expose] def ps : List (List (Fin 9 × Bool) × List (Fin 2 × Bool)) := ghWordsD.map fun r => (r, [])

@[expose] def posLetter (c : Int) : Fin 9 × Bool := (⟨(c.toNat - 1) % 9, Nat.mod_lt _ (by decide)⟩, true)

@[expose] def nfW (k : Nat) : List (Fin 9 × Bool) := (nfCodes k).map posLetter

@[expose] def nfs : List (List (Fin 9 × Bool)) := (List.range 512).map nfW

theorem chk : grpK 20 MA MB 2 5 (segs.map natW) (ps.map fun q => (natW q.1, natW q.2)) = true := by
  quickRfl

theorem dst : distK 20 MA MB 2 5 (segs.map natW) (nfs.map natW) = true := by
  quickRfl

end CertificateChecks.KernelHSGH

end
