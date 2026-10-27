module

public import Certificates.Kernel.SporSch.PairBT.McLSylFacts
public import Certificates.Kernel.SporSch.PairBT.McLSyl5E
public import Certificates.Kernel.SporSch.PairBT.McLSyl5Chk
public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Certificates.Kernel.SporSch.McLSylowProof
import Certificates.Kernel.SporSch.PairBT.McLSylFactsK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLSylK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.Schreier.PairMcL CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.McLSylChk

theorem facts2242 : countOrd bs 5 blocks = 37122624 := by
  have hp : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hN : ¬5 ^ (3 + 1) ∣ ordK PMcL.LR 5 := by
    rw [ord]
    decide
  have h := count_two_proved sz McLSylFacts.chainS base_nodup (by decide)
    (allN_spec PMcLCheck.perm 0 (by decide)) (allN_spec PMcLCheck.perm 1 (by decide))
    (p := 5) (k := 3) (e := 1) rfl (by decide) hN (XL := McLS5.XL) rfl McLS5.inc McLS5.he
    McLSyl5Chk.c1 McLSyl5Chk.c2 McLSyl5Chk.s1 McLSyl5Chk.s2 McLSyl5Chk.o1 McLSyl5Chk.o2
    McLSyl5Chk.b1 McLSyl5Chk.b2 (by decide) (by decide) (by decide) (bs := bs) (by decide)
    (groups := groups) (by decide)
  rw [ord] at h
  exact h

end CertificateChecks.KernelSporSch.McLSylK

end
