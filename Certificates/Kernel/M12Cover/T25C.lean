module

public import Certificates.Kernel.M12Cover.T25Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelM12T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.M12Trans
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow

theorem all_range {n : Nat} {f : Nat → Bool} : (List.range n).all f = true ↔ ∀ i < n, f i = true := by
  simp [List.all_eq_true, List.mem_range]

theorem rCodeC : rCodeCheck = true := by
  unfold rCodeCheck
  refine all_range.2 fun i hi => all_range.2 fun p hp => ?_
  rw [rCodeArr_get _ (by omega)]
  have e1 : (12 * i + p) / 12 = i := by omega
  have e2 : (12 * i + p) % 12 = p := by omega
  rw [e1, e2]
  exact beq_self_eq_true _

@[expose] noncomputable def fCO (i : Nat) : Bool :=
  (i == 0 || (decide (tpK i < i) && (tlK i == 1 || tlK i == 2))) &&
    [1, 2].all fun l => decide (taK l i < 1485) && decide (twK l i < 64) &&
      (List.range 12).all fun p =>
        r0K tpK tlK letterCode 1485 i (letterCode l p) ==
          SylowTable.nth 0 (SylowTable.code (twK l i)) (r0K tpK tlK letterCode 1485 (taK l i) p)

#lc_blocks COB fCO 1485 16

theorem cosetC : cosetCheck = true := by
  rw [cosetCheck_eq, r0_eq, tpar_eq, tlet_eq, tact_eq, twit_eq]
  exact all_range.2 fun i hi => CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) COB.all i hi

@[expose] noncomputable def fDC (i : Nat) : Bool :=
  (List.range 64).all fun h => decide (ppK i h < 64) && decide (ihK i h < 1485) &&
    (List.range 12).all fun p => rcK (12 * i + dCode h p) == dCode (ppK i h) (rcK (12 * ihK i h + p))

#lc_blocks DCB fDC 1485 8

theorem decompC : decompCheck = true := by
  rw [decompCheck_eq, tp_eq, tih_eq, rc_eq]
  exact all_range.2 fun i hi => CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) DCB.all i hi

@[expose] noncomputable def fBE (i : Nat) : Bool :=
  decide (aiK i < 64) && decide (sgK i < 1485) &&
    (List.range 12).all fun p =>
      rβCodeG (r0K tpK tlK letterCodeβ 1485) i p == dCode (aiK i) (rcK (12 * sgK i + p))

#lc_blocks BEB fBE 1485 32

theorem betaC : betaCheck = true := by
  rw [betaCheck_eq, r0β_eq, taIdx_eq, tsig_eq, rc_eq]
  unfold betaCheckG
  rw [decide_eq_true nodup_sig, Bool.true_and]
  exact all_range.2 fun i hi => CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) BEB.all i hi

@[expose] noncomputable def fQU (i : Nat) : Bool :=
  (List.range 64).all fun h =>
    mIdx (mIdx (invIdx (aiK i)) (bIdx (ppK i h))) (aiK (ihK i h)) == ppK (sgK i) (bIdx h)

#lc_blocks QUB fQU 1485 16

theorem quotC : quotCheck = true := by
  rw [quotCheck_eq, taIdx_eq, tsig_eq, tp_eq, tih_eq]
  exact all_range.2 fun i hi => CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) QUB.all i hi

@[expose] noncomputable def fLA (h : Nat) : Bool :=
  (LamSumG aiK ppK ihK h + muIdx h + muIdx (bIdx h)) % 2 == lamIdx h

#lc_blocks LAB fLA 64 1

theorem lamC : lambdaCheck = true := by
  rw [lambdaCheck_eq, taIdx_eq, tp_eq, tih_eq]
  exact all_range.2 fun h hh => CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) LAB.all h hh

end CertificateChecks.KernelM12T

end
