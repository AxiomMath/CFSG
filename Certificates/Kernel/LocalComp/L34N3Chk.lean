module

public import Certificates.Kernel.LocalComp.L34N3Data
public import Certificates.Kernel.LocalComp.L34NDefs
public import Certificates.Kernel.LocalComp.L34SChk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34N3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X
open CFSG.KC.HeAutK (cntR)
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def tot (c : Nat) : Nat :=
  cntR (fun q => Nat.beq (L34N.J q % 32 / 8) (c + 1)) 0 7755

@[expose] noncomputable def orb (c : Nat) : Bool :=
  orbK 42 6 6 L34R.G GI (OT c) (OE c) (OS c) (OSI c) (ON c) 12 (L34R.T (KR c))

@[expose] noncomputable def cent (c : Nat) : Bool :=
  centK 42 6 20160 L34S.T (L34R.T (KR c)) (CN c) (CX c) (CP c)

theorem kTot0 : Nat.beq (tot 0) 1920 = true := by quickRfl
theorem kTot1 : Nat.beq (tot 1) 2240 = true := by quickRfl
theorem kTot2 : Nat.beq (tot 2) 672 = true := by quickRfl

theorem kOrb0 : orb 0 = true := by quickRfl
theorem kOrb1 : orb 1 = true := by quickRfl
theorem kOrb2 : orb 2 = true := by quickRfl

theorem kCent0 : cent 0 = true := by quickRfl
theorem kCent1 : cent 1 = true := by quickRfl
theorem kCent2 : cent 2 = true := by quickRfl

theorem kNegT : notB (Nat.beq (tot 2) 671) = true := by quickRfl

theorem kNegO : andB (notB (orbK 42 6 6 L34R.G GI (OT 2) (OE 2) (OS 2) (OSI 2) 671 12
    (L34R.T (KR 2)))) (notB (orbK 42 6 6 L34R.G GI (OT 2) (OE 2) (OS 2) (OSI 2) 672 12
    (L34R.T (KR 1)))) = true := by quickRfl

theorem kNegC : notB (centK 42 6 20160 L34S.T (L34R.T (KR 2)) 59 (CX 2) (CP 2)) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34N3

end
