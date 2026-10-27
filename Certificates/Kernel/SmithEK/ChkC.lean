module

public import Certificates.Kernel.SmithEK.CChk
public import Certificates.Kernel.SmithEK.CWords
public import Certificates.Kernel.SmithEK.ChkE
public import Certificates.Kernel.SmithEK.ChkT
public import CFSG.Certificates.Kernel.SmithEK.CSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem uPts_size : (CFSG.F4.Native.uPts ()).size = 693 := by
  rw [uPts_eq, List.size_toArray, pts_length]

theorem tables_R : ∀ m < 693, ∀ q < 693,
    CFSG.Sporadic.Th.Native.ap (CFSG.KC.U6.tvTabsG CFSG.F4.Native.uPts CFSG.F4.Native.uPos)[m]! q =
      CFSG.KLie.CT.fget (CertificateChecks.KernelU6.T.R m) q 10 := fun m hm q hq =>
  (CFSG.KC.U6.tables_sound CertificateChecks.KernelU6.up_eq CertificateChecks.KernelU6.pos_eq
    CertificateChecks.KernelU6.kTables m hm).2.2 q hq

theorem chkTvInv_eq : chkTvInv = true := chkTvInv_of tvArr_cs c21260conj

theorem chkTvConj_eq : chkTvConj = true := chkTvConj_of tvArr_cs uPts_size tables_R c21260conj

theorem ptImg_R : ∀ j < 693, ∀ b < 693, ptImg j b = fldR CertificateChecks.KernelU6.T.R j b ∧
    fldR CertificateChecks.KernelU6.T.R j b < 693 := fun j hj b hb =>
  ⟨ptImg_eq uPts_size tables_R hj hb, ((rows_of c21260conj j hj).2 b hb).1⟩

theorem chkPtWords_eq : chkPtWords = true := chkPtWords_of ptImg_R c21260pt_len c21260pt

theorem chkPairWords_eq : chkPairWords = true :=
  chkPairWords_of ptImg_R uPts_eq c21260pair_len c21260pair

theorem lane_tv {k : Nat} (hk : k < 693) (v : Nat) :
    fld k (c8ap tp.C v) = applyCols tvArr[k]! v := by
  have hk' : k < pts.L.length := by rw [pts_length]; exact hk
  rw [c8ap_eq, applyL_fld, packOK_sound _ _ _ tp_ok k hk', tvArr_get hk, tvCols_eq,
    ← tvW_cTabQ, ← cT_eq, applyCols_toArray]

theorem chkPlaneWords_eq : chkPlaneWords = true :=
  chkPlaneWords_of chkW_eq chkT_eq (fun k hk v => lane_tv hk v)
    (fun i hi => (wtArr_wd hi).symm) c21260plane_len c21260plane

end CertificateChecks.KernelSmithEK
