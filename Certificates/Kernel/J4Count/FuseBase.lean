
module

public import Certificates.Kernel.J4Count.FuseChecks
public import Certificates.Kernel.SporSch.J4S.Regs
public import CFSG.Certificates.Kernel.SporSch.J4SPairSound
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.H13.J4ClassCheckInputs

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Fuse

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier
open CFSG.Quasithin.H13.J4 (uP vP dP tP cnjP conjEqP lettersOK)

theorem hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6 := CertificateChecks.KernelJ4Q.hK

theorem regs_ok : RegOK one regsN RG :=
  runPK_ok hK typeIIProg CertificateChecks.KernelSporSch.J4Regs.init_ok
    CertificateChecks.KernelSporSch.J4Regs.lts

theorem reg_ok {r : Nat} (hr : r < 9) : PairOK regsN[r]! (reg r).1 (reg r).2 := by
  simp only [reg]
  exact regs_ok.2.2 r hr

theorem x_ok : PairOK Xn (reg 1).1 (reg 1).2 := reg_ok (by norm_num)

theorem y_ok : PairOK Yn (reg 2).1 (reg 2).2 := reg_ok (by norm_num)

theorem t_ok : PairOK Tn (reg 3).1 (reg 3).2 := reg_ok (by norm_num)

theorem a_ok : PairOK An A A :=
  ⟨CertificateChecks.KernelSporSch.J4Real.hA, CertificateChecks.KernelSporSch.J4Real.hA⟩

theorem b_ok : PairOK Bn B Bi :=
  ⟨CertificateChecks.KernelSporSch.J4Real.hB, CertificateChecks.KernelSporSch.J4Real.hB3⟩

theorem pm_ok {P Q : Pair} {p q : Nat × Nat} (hP : PairOK P p.1 p.2) (hQ : PairOK Q q.1 q.2) :
    PairOK (mulP P Q) (pm p q).1 (pm p q).2 := mulP_ok hK hP hQ

theorem pinv_ok {P : Pair} {p : Nat × Nat} (hP : PairOK P p.1 p.2) :
    PairOK (invP P) (pinv p).1 (pinv p).2 := invP_ok hP

theorem ppow_ok {P : Pair} {p : Nat × Nat} (hP : PairOK P p.1 p.2) (e : Nat) :
    PairOK (powP P e) (ppow p e).1 (ppow p e).2 := powP_ok hK hP e

theorem d_ok : PairOK Dn DK.1 DK.2 :=
  pm_ok (pm_ok (ppow_ok (pm_ok y_ok x_ok) 4) (pinv_ok y_ok)) x_ok

theorem z_ok : PairOK Zn ZK.1 ZK.2 :=
  ppow_ok (pm_ok (pm_ok (pm_ok y_ok (pinv_ok d_ok)) t_ok) d_ok) 3

theorem uLetters_ok : lettersOK (CFSG.Quasithin.H13.J4.Native.uLetters ()) = true := by decide +kernel

theorem vLetters_ok : lettersOK (CFSG.Quasithin.H13.J4.Native.vLetters ()) = true := by decide +kernel

end CertificateChecks.KernelJ4Count.Fuse

end
