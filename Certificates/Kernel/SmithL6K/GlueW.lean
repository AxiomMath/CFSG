module

public import Certificates.Kernel.SmithL6K.GlueG
public import Certificates.Kernel.SmithL6K.Meet
public import Certificates.Kernel.SmithL6K.ChecksW
public import CFSG.Certificates.Kernel.SmithL6KWSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel

theorem wt_inj : ∀ i < 1395, ∀ j < 1395, wt i = wt j → i = j := by
  have hn := CFSG.Decide.nodup_of_bitsetNodup_nat wtd_nodup
  intro i hi j hj e
  rw [wt_eq hi, wt_eq hj, getD_of_lt (by rw [wtd_length]; exact hi),
    getD_of_lt (by rw [wtd_length]; exact hj)] at e
  exact (List.Nodup.getElem_inj_iff hn).mp e

theorem ann_eq {j : Nat} (hj : j < 1395) : setM (annArr[j]!) = annS (setM (wMask j)) := by
  have h := wData_lt hj
  have e1 : wMask j = spanMask (wData[j]! % 64) (wData[j]! / 64 % 64) (wData[j]! / 4096) := rfl
  have e2 : annArr[j]! = annMaskOf (wData[j]! % 64) (wData[j]! / 64 % 64) (wData[j]! / 4096) := by
    rw [annArr_get hj]
    rfl
  rw [e1, e2, annS_span (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by omega)]

theorem wtP_eq {i : Nat} (hi : i < 1395) : fldW 20 wtP i = wt i := by
  have e := pinF_get pin_wtP (s := i) (by rw [wtd_length]; exact hi)
  rw [Nat.zero_add] at e
  rw [e, wt_eq hi, getD_of_lt (by rw [wtd_length]; exact hi)]

theorem wmP_eq {i : Nat} (hi : i < 1395) : fldW 64 wmP i = wMask i := by
  have e := pinF_get pin_wmP (s := i) (by rw [wmk_length]; exact hi)
  rw [Nat.zero_add] at e
  rw [e, wMask_eq hi, getD_of_lt (by rw [wmk_length]; exact hi)]

theorem close_rows : ∀ s < 6, closeRowK (tcl.getD (gns.getD s 0) []) (fldW 12 tcP (gns.getD s 0))
    (gpP.getD s 0) wtP wmP = true
  | 0, _ => close_ok0
  | 1, _ => close_ok1
  | 2, _ => close_ok2
  | 3, _ => close_ok3
  | 4, _ => close_ok4
  | 5, _ => close_ok5

theorem clo_gns : ∀ s < gns.length, Clo (gns.getD s 0) := by
  intro s hs
  have hg := gns_lt s hs
  have h := close_rows s (by rw [gns_len] at hs; exact hs)
  rw [← tvCols_eq hg, fld_tcP hg] at h
  exact clo_of_closeRowK hg (fun _ hi => wtP_eq hi) (fun _ hi => wmP_eq hi) h

theorem tw_holds : chkTW = true :=
  chkTW_of gns_lt gns_zero reach_gns clo_gns wt_inj fun _ hj => ann_eq hj

end CertificateChecks.KernelSmithL6K
