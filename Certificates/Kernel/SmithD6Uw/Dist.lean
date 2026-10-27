module

public import Certificates.Kernel.SmithD6Uw.Glue
public import Certificates.Kernel.SmithD6Uw.DistChecks
public import Certificates.Kernel.SmithD6Kc.MeetFacts
public import CFSG.Certificates.Kernel.SmithD6DistSound
public import CFSG.Certificates.Kernel.SmithD6RankSound

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Uw

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6 CertificateChecks.SmithD6Kc

section Model

variable (hpb : ∀ i < 75735, pbArr[i]! = J.pbC.flatten.getD i #[])
  (hpp : ∀ i < 75735, ppArr[i]! = J.ppC.flatten.getD i #[])
include hpb hpp

theorem distD_zero_eq {j : ℕ} (hj : j < 75735) : distD 0 j = pkGet JU.uwK 2 j := by
  change (if meetCnt 0 j == 1 then 3 else if meetCnt 0 j == 4 then 2
    else if meetCnt 0 j == 16 then 1 else 0) = _
  rw [kcDist_eq, meetCnt_eq_d6MeetK hpb hpp (by norm_num) hj]
  obtain ⟨e1, e2, hk⟩ := pb_flat_getD hj
  have hc : j / 2048 < 37 := by omega
  have h := d6DistOK_sound (uwDistChunks_ok (j / 2048) hc) (j % 2048) hk
  rw [Nat.div_add_mod] at h
  unfold d6MeetK
  rw [(d6PB_eq hj).1, (d6PB_eq hj).2, e1, e2]
  exact h

variable (hW : wtArr.toList = J.wtC.flatten)
include hW

theorem uw7ChkDist_of_pinned : uw7ChkDist () = true := by
  unfold uw7ChkDist
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  rw [uw7Cls_eq hW hj', distD_zero_eq hpb hpp hj', beq_self_eq_true]

end Model

end CertificateChecks.SmithD6Uw

end
