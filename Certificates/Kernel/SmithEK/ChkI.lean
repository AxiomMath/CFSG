module

public import Certificates.Kernel.SmithEK.BasChk
public import Certificates.Kernel.SmithEK.IPairsA
public import Certificates.Kernel.SmithEK.IPairsB
public import Certificates.Kernel.SmithEK.ChkW
public import Certificates.Kernel.SmithEK.Span
public import CFSG.Certificates.Kernel.SmithEK.ISound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree ipairs_all
  (fun c => chunkI (wBits wd.W ||| 1) pts.L (bs.L.map spanM) (87 * c) 87 = true) 8
  CertificateChecks.KernelSmithEK.c21107pair_

theorem bs_length : bs.L.length = 693 := (basOK_sound _ _ _ bs_ok).1.trans pts_length

theorem ms_get {k : Nat} (hk : k < 693) :
    (bs.L.map spanM).getD k 0 = spanM (bs.L.getD k []) := by
  simp [List.getD_eq_getElem?_getD, bs_length, hk]

theorem chkI_eq_true : chkI = true := by
  refine chkI_of (T := cT.L) (W := wd.W) (Bs := bs.L) uPts_eq pts_length (fun k _ => ?_)
    tvW_length bs_ok (fun k hk l hl hkl => ?_) (isWt_of (M := wd.M) wd_len wd_ok (fun i hi => ?_))
  · rw [tvCols_eq, ← tvW_cTabQ, ← cT_eq]
  · have hc : k / 87 < 8 := by omega
    have e := chunkI_sound (ipairs_all (k / 87) hc) (Nat.mod_lt k (by omega : 87 > 0)) (j := l)
      (by rw [Nat.div_add_mod]; exact hkl) (by rw [pts_length]; exact hl)
    rw [Nat.div_add_mod, ms_get hk, ms_get hl] at e
    exact e
  · have hc : i / 64 < 14 := by omega
    have e := pinChunkK_sound (pins_all (i / 64) hc) (Nat.mod_lt i (by omega : 64 > 0))
      (by rw [wData_len, Nat.div_add_mod]; exact hi)
    rwa [Nat.div_add_mod] at e

end CertificateChecks.KernelSmithEK
