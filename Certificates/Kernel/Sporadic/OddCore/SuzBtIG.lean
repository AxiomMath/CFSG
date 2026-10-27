module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtZG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtIF
public import CFSG.Certificates.Kernel.Spor.BTupISound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtIG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG


theorem hrM : ∀ i < SuzBtM1.cnt, btRtK 8 8 SuzBtM1.cnt SuzBtM1Z.S SuzBtM1.R SuzBtM1.POS
    SuzBtM1Z.RT i = true := fun i hi =>
  btRtSl_spec SuzBtZF.kRt (Nat.zero_le _) (by rw [SuzBtF.kCnt] at hi; omega) hi

theorem kI_eq : btCntN SuzBtM1.cnt (btInvP 8 33 (mask 33) SuzBtL1.cnt SuzBtM1.K SuzBtM1.R
    SuzBtM1Z.RT SuzBtL1.K) = 288 := Nat.beq_eq.mp SuzBtIF.kI

theorem card_inv_m1 : Nat.card {x : decSubgroup m1Decs // x * x = 1 ∧ x ≠ 1 ∧
    ((x : decSubgroup m1Decs) : Equiv.Perm (Fin 1782)) ∉ decSubgroup l1Decs} = 288 := by
  rw [← (show genSub 1782 8 mgp = decSubgroup m1Decs from genSub_dec m1Decs), ← l1_eq, ← kI_eq]
  refine card_inv_of_btInvP hgM hpM hfixM hbM hSM hrM (by norm_num) SuzBtF.kHd
    (fun q hq => btKey_mem hgL hbL hpL hq) (fun l hl _ => btKey_cover hgL hbL hpL SuzBtZF.kL1Hd hl)
    (fun q hq => (ptFacts (hpL q hq)).canon)
    (fun x hx l hl e => invE1_ext (m1_le hx) (l1_le hl) e)

end CertificateChecks.KernelSpor.SuzBtIG

end
