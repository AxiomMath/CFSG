
module

public import Certificates.Kernel.J4Count.Fix5Base

public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase1

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Five

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.J4.Struct CertificateChecks.KernelSporSch
open CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4Five
open CertificateChecks.KernelJ4Q CFSG.QuasithinUnique.A5
open scoped Classical

theorem fixCard_qA :
    fixCard qA = 128 := by
  rw [qA_eq, fixCard_eq_card _
    (fun a => Nat.beq (Nat.mod (etaV unMats QAN a) (Nat.pow 2 112)) QAN = true) ?_]
  · have h := Nat.eq_of_beq_eq_true fix_qA
    unfold cntQA at h
    rw [J4NoCP.cntK_eq] at h
    refine Eq.trans (congrArg Finset.card (Finset.filter_congr fun a _ => ?_)) h
    rw [J4NoCP.etaV_eq]
  · intro a _
    rw [η_smul_toRow, ← ofRow_inj, Nat.beq_eq]
    change toVecD 112 _ = toVecD 112 _ ↔ etaV unMats QAN a % 2 ^ 112 = QAN
    rw [toVecD_eq_iff, Nat.mod_eq_of_lt (b := 2 ^ 112) (by norm_num [QAN] : QAN < 2 ^ 112)]

end CertificateChecks.KernelJ4Count.Five

end
