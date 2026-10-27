module

public import Certificates.Kernel.SporSch.PairBT.McLSylFacts
public import Certificates.Kernel.SporSch.PairBT.McLSyl2E
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

theorem facts2243 : countOrd bs 2 blocks = 22275 := by
  have hN : ¬2 ^ (7 + 1) ∣ ordK PMcL.LR 5 := by
    rw [ord]
    decide
  have h := count_one_proved sz McLSylFacts.chainS base_nodup
    (allN_spec PMcLCheck.perm 0 (by decide)) (allN_spec PMcLCheck.perm 1 (by decide)) cA
    (p := 2) (k := 7) (e := 1) rfl (by decide) oA hN (XL := McLS2.XL) rfl McLS2.inc McLS2.he
    (d := McLCK.getD 0 clsD0) McLSylFacts.clsOK (Nat.eq_of_beq_eq_true McLSylFacts.hR0)
    (bs := bs) (by decide) (groups := groups) (by decide)
  rw [Nat.eq_of_beq_eq_true McLSylFacts.dc0] at h
  exact h

end CertificateChecks.KernelSporSch.McLSylK

end
