module

public import Certificates.Data.Kernel.Griess13.Glue
public import Certificates.Data.Kernel.M1F2
public import CFSG.Monster.GMS.Griess13.GlueCertData
public import Certificates.Kernel.Griess13.Data
public meta import Certificates.Kernel.Griess13.GlueGen
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_eval CertificateChecks.KernelG13 GD CertificateChecks.KernelG13.stepGlue

#ks_chars CertificateChecks.KernelG13.Slp2 CFSG.Monster.GMS.Griess13.Co1Data.slpMax2

#ks_chars CertificateChecks.KernelG13.SlpAB CFSG.Monster.GMS.Griess13.Co1Data.slpWordsAB

#ks_chars CertificateChecks.KernelG13.TB CFSG.Monster.GMS.Griess13.Co1Data.tmatBits

namespace CertificateChecks.KernelG13

open CFSG.KC.G13 CFSG.KC.Co1B CFSG.KC.M1F2 CertificateChecks.KernelCo1Cover
  CFSG.Monster.GMS.Griess13.Co1Data

@[expose] noncomputable def slp2 : SLP := decSLP GD.s2L GD.s2O

@[expose] noncomputable def slpAB : SLP := decSLP GD.sabL GD.sabO

@[expose] noncomputable def tmatC (i : Nat) : List Char := 'T' :: '\n' :: (TB.chars.drop (576 * i)).take 576

theorem slp2_text : charsEq Slp2.chars (slpC slp2) = true := by quickRfl

theorem slpAB_text : charsEq SlpAB.chars (slpC slpAB) = true := by quickRfl

theorem h_ok : evalP slp2 [pk R0 R0, pk R1 G.B2] = GD.H := by decide +kernel

theorem g_ok : wordP GD.H (parseWord gStr) = GD.G := by decide +kernel

theorem x_ok : ∀ k : Fin 3, wordP [G.N1, G.N2] (parseWord (xStr k)) = GD.X.getD k.val 0 := by
  decide +kernel

theorem y_ok : ∀ k : Fin 3, wordP [G.N1, G.N2] (parseWord (yStr k)) = GD.Y.getD k.val 0 := by
  decide +kernel

theorem ab_ok : evalP slpAB [G.N1, G.N2, GD.G] = GD.AB := by decide +kernel

theorem tm_ok : ∀ i < 8, m1Bind (tmatC i) 24 (GD.T.getD i 0) = true := by decide +kernel

@[expose] noncomputable def elK (r : Nat) : Nat := eqMaskK (GD.X.getD (r / 576) 0) (r % 576 / 24) (r % 24)

theorem el0 : ∀ r < 216, elK r = GD.E.getD r 0 := by decide +kernel
theorem el1 : ∀ r < 216, elK (216 + r) = GD.E.getD (216 + r) 0 := by decide +kernel
theorem el2 : ∀ r < 216, elK (432 + r) = GD.E.getD (432 + r) 0 := by decide +kernel
theorem el3 : ∀ r < 216, elK (648 + r) = GD.E.getD (648 + r) 0 := by decide +kernel
theorem el4 : ∀ r < 216, elK (864 + r) = GD.E.getD (864 + r) 0 := by decide +kernel
theorem el5 : ∀ r < 216, elK (1080 + r) = GD.E.getD (1080 + r) 0 := by decide +kernel
theorem el6 : ∀ r < 216, elK (1296 + r) = GD.E.getD (1296 + r) 0 := by decide +kernel
theorem el7 : ∀ r < 216, elK (1512 + r) = GD.E.getD (1512 + r) 0 := by decide +kernel

theorem el_len : GD.E.length = 1728 := by decide +kernel

theorem span_ok : spanCheckL GD.E (fmaskOf freePos) certTab = true := by decide +kernel

theorem seventh_ok : ∀ c : Fin 8 → ZMod 2,
    eqK (powW (mulWK GD.G (comboK GD.T c)) 7) oneK = true → eqK (comboK GD.T c) oneK = true := by
  decide +kernel

end CertificateChecks.KernelG13

end
