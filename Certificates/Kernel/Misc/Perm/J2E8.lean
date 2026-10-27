module

public import Certificates.Kernel.Misc.Perm.J2Rel
public import CFSG.RankThree.PartTwo.Sec17.J2CoverE8Inputs
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartTwo.Sec17.J2CoverE8Inputs

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelMisc.J2Fam.E8V1 9 CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2E8v1Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.E8V2 9 CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2E8v2Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.E8S 9 CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2E8sArr
#ks_perm CertificateChecks.KernelMisc.J2Fam.E8U1 9 CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2E8u1Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.E8U2 9 CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2E8u2Arr
#ks_perm CertificateChecks.KernelMisc.J2Fam.E8T 9 CFSG.RankThree.PartTwo.Sec17.J2CoverE8.j2E8tArr

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec17.J2CoverE8
open CertificateChecks.KernelMisc.J2C3 (cm I)

theorem rE8v1 : R j2E8v1Arr E8V1 := ⟨arrBind_sound (by quickRfl), by quickRfl⟩
theorem rE8v2 : R j2E8v2Arr E8V2 := ⟨arrBind_sound (by quickRfl), by quickRfl⟩
theorem rE8s : R j2E8sArr E8S := ⟨arrBind_sound (by quickRfl), by quickRfl⟩
theorem rE8u1 : R j2E8u1Arr E8U1 := ⟨arrBind_sound (by quickRfl), by quickRfl⟩
theorem rE8u2 : R j2E8u2Arr E8U2 := ⟨arrBind_sound (by quickRfl), by quickRfl⟩
theorem rE8t : R j2E8tArr E8T := ⟨arrBind_sound (by quickRfl), by quickRfl⟩

theorem chkJ2E8_K : chkJ2E8 = true := by
  have v12 := rE8v1.comp rE8v2
  have u12 := rE8u1.comp rE8u2
  have w1 := rE8v1.comp rE8u1
  have w2 := rE8v2.comp rE8u2
  unfold chkJ2E8 j2E8v12Arr j2E8u12Arr j2E8w1Arr j2E8w2Arr
  rw [rE8v1.ok (by quickRfl) (by quickRfl), rE8v2.ok (by quickRfl) (by quickRfl),
    rE8s.ok (by quickRfl) (by quickRfl), rE8u1.ok (by quickRfl) (by quickRfl),
    rE8u2.ok (by quickRfl) (by quickRfl), rE8t.ok (by quickRfl) (by quickRfl),
    (rE8v1.comp rE8v1).eq R.id, (rE8s.conj rE8v1).eq rE8v2, (rE8s.conj rE8v2).eq v12,
    (rE8u1.comp rE8u1).eq R.id, (rE8t.conj rE8u1).eq rE8u2, (rE8t.conj rE8u2).eq u12,
    rE8v1.commA rE8u1, rE8v1.commA rE8u2, rE8v2.commA rE8u1, rE8v2.commA rE8u2,
    rE8v1.commA rE8t, rE8v2.commA rE8t,
    rE8v1.eq R.id, rE8v2.eq R.id, rE8v2.eq rE8v1, v12.eq R.id,
    rE8u1.eq R.id, rE8u2.eq R.id, rE8u2.eq rE8u1, u12.eq R.id,
    rE8u1.eq rE8v1, rE8u1.eq rE8v2, rE8u1.eq v12,
    w1.eq R.id, w2.eq R.id, w2.eq w1, (w1.comp w2).eq R.id]
  quickRfl

theorem neg_conj : (!Nat.beq (cm E8S (cm E8U1 (iv E8S))) E8V2) = true := by quickRfl

theorem neg_comm : (!Nat.beq (cm E8V1 E8S) (cm E8S E8V1)) = true := by quickRfl

theorem neg_sift :
    (!siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2M5.C.LR J2M5.C.TRI J2M5.C.BP 3 0 OU) =
      true := by
  quickRfl

end CertificateChecks.KernelMisc.J2Fam

end
