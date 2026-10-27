module

public import CFSG.Certificates.Kernel.Fi22LHSound
public import Certificates.Kernel.Fi22LH.Sel
import Certificates.Kernel.Fi22LH.Tall0
import Certificates.Kernel.Fi22LH.Tall1
import Certificates.Kernel.Fi22LH.Tall2
import Certificates.Kernel.Fi22LH.Tall3
import Certificates.Kernel.Fi22LH.Tall4
import Certificates.Kernel.Fi22LH.Tall5
import Certificates.Kernel.Fi22LH.Fix0
import Certificates.Kernel.Fi22LH.SetA0
import Certificates.Kernel.Fi22LH.SetA1
import Certificates.Kernel.Fi22LH.SetB0
import Certificates.Kernel.Fi22LH.SetB1
import Certificates.Kernel.Fi22LH.Orb
import Certificates.Kernel.Fi22LH.Root
import Certificates.Kernel.Fi22LH.Row
import Certificates.Kernel.Fi22LH.Far
import Certificates.Kernel.Fi22LH.Mu
import Certificates.Kernel.Fi22LH.Ed
import Certificates.Kernel.Fi22LH.Bind
import Certificates.Kernel.Fi22Core.OrbData
import Certificates.Kernel.Fi22LH.OrbOK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH CFSG.Sporadic.Fi22.Native

@[expose] noncomputable def lhD : LHData :=
  ⟨R, Z, QA, QB, P, X, Y, C, M, G, TF, ph, al, be, bi, op, ol, u, lb0, lb1, eb, h0, h1, h2, up, pd,
    qa, qb, qbi, rq0, rq1, cq0, cq1, mq, ml, mt⟩

theorem lb0_eq : ∀ j < 351, ent lb0 j = ((lhData ())[0]!)[j]! := by decide +kernel
theorem lb1_eq : ∀ j < 351, ent lb1 j = ((lhData ())[1]!)[j]! := by decide +kernel
theorem pd_eq : ∀ i < 693, fld(pd, 10 * i, 1023) = phiData[i]! := by decide +kernel

theorem lhD_checks : LHChecks lhD := by
  refine ⟨Nat.eq_of_beq_eq_true al_eq, Nat.eq_of_beq_eq_true be_eq, Nat.eq_of_beq_eq_true op_eq,
    Nat.eq_of_beq_eq_true ol_eq, lb0_eq, lb1_eq, pd_eq, fun s hs => ?_, fun s hs => ?_, bi_ok,
    fun s hs => ?_, fun s hs => ?_, bfsA, bfsB, walkA, walkB, notIn, flat, fun l hl => ?_, root_0,
    root_1, comm_0, comm_1, fun s hs => ?_, fun s hs => ?_, rowInv, up_ok, star, fail, swap, far,
    fun s hs => ?_, mu_tree, ml_ok, fun s hs => ?_⟩
  · interval_cases s
    exacts [tall_0, tall_1, tall_2, tall_3, tall_4, tall_5, tall_6, tall_7, tall_8, tall_9,
      tall_10, tall_11, tall_12, tall_13, tall_14, tall_15, tall_16, tall_17, tall_18, tall_19,
      tall_20, tall_21, tall_22, tall_23, tall_24, tall_25]
  · interval_cases s
    exacts [fix_0, fix_1, fix_2, fix_3, fix_4, fix_5]
  · interval_cases s
    exacts [setA_0, setA_1, setA_2, setA_3, setA_4, setA_5, setA_6, setA_7, setA_8, setA_9,
      setA_10, setA_11, setA_12, setA_13, setA_14, setA_15, setA_16, setA_17, setA_18, setA_19]
  · interval_cases s
    exacts [setB_0, setB_1, setB_2, setB_3, setB_4, setB_5, setB_6, setB_7, setB_8, setB_9,
      setB_10, setB_11, setB_12, setB_13, setB_14, setB_15, setB_16, setB_17, setB_18, setB_19]
  · interval_cases l
    exacts [phi_0, phi_1, phi_2, phi_3, phi_4, phi_5, phi_6]
  · interval_cases s
    exacts [dom_0, dom_1, dom_2, dom_3]
  · interval_cases s
    exacts [row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7]
  · interval_cases s
    exacts [mu_0, mu_1, mu_2, mu_3]
  · interval_cases s
    exacts [ed_0, ed_1, ed_2, ed_3, ed_4, ed_5, ed_6, ed_7]

theorem lh_certificate : lhCertificate () = true := by
  unfold lhCertificate
  change lhChecks (orbitData ()) (tauAll (orbitData ())) (lhCompute (orbitData ()) (tauAll (orbitData ()))) = true
  rw [KernelFi22C.orbitData_eq, lhCompute_eq lhD orbOK lhD_checks]
  exact lhChecks_lhDec lhD orbOK lhD_checks

end CertificateChecks.KernelFi22LH
