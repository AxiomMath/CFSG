module

public import Certificates.Kernel.SmithEK.CWChk
public import Certificates.Kernel.SmithEK.Span
public import CFSG.Certificates.Kernel.SmithEK.CWSound
public import CFSG.Certificates.Kernel.SmithEK.ISound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem cs_len_cw : cs.L.length = 693 := by
  rw [← cs_ok, List.length_map, pts_length]

theorem chkCommWt_eq : CFSG.LargeExtraspecial.S14.SMI.chkCommWt = true := by
  refine chkCommWt_of cs_len_cw (fun k hk => ?_)
    (isWt_of (M := wd.M) wd_len wd_ok (fun i hi => ?_)) cw_ok
  · have hk' : k < pts.L.length := by rw [pts_length]; exact hk
    rw [tvCols_eq, ← tvW_cTabQ, ← cT_eq, ← cs_ok]
    simp [List.getD_eq_getElem?_getD, hk']
  · have hc : i / 64 < 14 := by omega
    have e := pinChunkK_sound (pins_all (i / 64) hc) (Nat.mod_lt i (by omega : 64 > 0))
      (by rw [wData_len, Nat.div_add_mod]; exact hi)
    rwa [Nat.div_add_mod] at e

end CertificateChecks.KernelSmithEK
