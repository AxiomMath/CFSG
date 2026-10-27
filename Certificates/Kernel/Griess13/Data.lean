module

public import Certificates.Data.Kernel.Griess13.Packed
public import Certificates.Kernel.Co1Cover.Data
public import CFSG.Monster.GMS.Griess13.ChecksInputs
public meta import Certificates.Kernel.Griess13.Gen
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Eval
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 100000

#kc_eval CertificateChecks.KernelG13 G CertificateChecks.KernelG13.stepG13

#ks_chars CertificateChecks.KernelG13.Slp CFSG.Monster.GMS.Griess13.Co1Data.slpMax11

namespace CertificateChecks.KernelG13

open CFSG.KC.G13 CFSG.KC.Co1B CertificateChecks.KernelCo1Cover CFSG.Monster.GMS.Griess13.Co1Data

@[expose] noncomputable def slp : CFSG.Monster.GMS.Griess13.Co1Data.SLP := decSLP G.slpL G.slpO

@[expose] noncomputable def eK (i : Fin 6) : Nat := G.E.getD i.val 0

@[expose] noncomputable def mK (i : Fin 2) : Nat := G.M.getD i.val 0

@[expose] noncomputable def rK (k : Fin 12) : Nat := G.R.getD k.val 0

@[expose] noncomputable def nK (s : Fin 2) : Nat := [G.N1, G.N2].getD s.val 0

theorem slp_text : charsEq Slp.chars (slpC slp) = true := by quickRfl

theorem b2_ok : Nat.beq (mulWK R1 R1) G.B2 = true := by quickRfl

theorem n_ok : evalP slp [pk R0 R0, pk R1 G.B2] = [G.N1, G.N2] := by decide +kernel

theorem e_ok : ∀ i : Fin 6, wordP [G.N1, G.N2] (parseWord (eStr i)) = eK i := by decide +kernel

theorem t_ok : wordP [G.N1, G.N2] (parseWord tauStr) = G.T := by decide +kernel

theorem m_ok : ∀ i : Fin 2, wordP [G.N1, G.N2] (parseWord (mStr i)) = mK i := by decide +kernel

theorem r_ok : ∀ k : Fin 12, wordP [G.N1, G.N2] (parseWord (repStr k)) = rK k := by decide +kernel

theorem iotaNe_ok : iotaNeK eK = true := by quickRfl

end CertificateChecks.KernelG13

end
