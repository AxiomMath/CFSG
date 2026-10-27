module

public import Certificates.Kernel.J4Fam.Data
public import Certificates.Data.Kernel.J4Fam
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Fam

open CFSG.KC.J4Fam
open CFSG.KC (notB)

theorem lv0_ok' : (LV0 == [0]) = true := by quickRfl

theorem lv7_nil' : LV7.isEmpty = true := by quickRfl

theorem lv0_ok : LV0 = [0] := beq_iff_eq.mp lv0_ok'

theorem lv7_nil : LV7 = [] := List.isEmpty_iff.mp lv7_nil'

theorem lens_lv : (LV0.length == 1 && LV1.length == 191 && LV2.length == 2091 &&
    LV3.length == 3643 && LV4.length == 1449 && LV5.length == 130 && LV6.length == 2) = true := by
  quickRfl

theorem tg_ok : (TG0.length == LV0.length && TG1.length == LV1.length && TG2.length == LV2.length &&
    TG3.length == LV3.length && TG4.length == LV4.length && TG5.length == LV5.length &&
    TG6.length == LV6.length) = true := by quickRfl

theorem cv_ok0 : coverOK LV1.length TG0 = true := by quickRfl
theorem cv_ok1 : coverOK LV2.length TG1 = true := by quickRfl
theorem cv_ok2 : coverOK LV3.length TG2 = true := by quickRfl
theorem cv_ok3 : coverOK LV4.length TG3 = true := by quickRfl
theorem cv_ok4 : coverOK LV5.length TG4 = true := by quickRfl
theorem cv_ok5 : coverOK LV6.length TG5 = true := by quickRfl
theorem cv_ok6 : coverOK LV7.length TG6 = true := by quickRfl

theorem tr_ok : (treeOK LVT0 LV0 && treeOK LVT1 LV1 && treeOK LVT2 LV2 && treeOK LVT3 LV3 &&
    treeOK LVT4 LV4 && treeOK LVT5 LV5 && treeOK LVT6 LV6 && treeOK LVT7 LV7 && treeOK FBT FB &&
    treeOK FLLT FLL) = true := by quickRfl

theorem tg_tr0 : treeOK TGT0 TG0 = true := by quickRfl
theorem tg_tr1 : treeOK TGT1 TG1 = true := by quickRfl
theorem tg_tr2 : treeOK TGT2 TG2 = true := by quickRfl
theorem tg_tr3 : treeOK TGT3 TG3 = true := by quickRfl
theorem tg_tr4 : treeOK TGT4 TG4 = true := by quickRfl
theorem tg_tr5 : treeOK TGT5 TG5 = true := by quickRfl
theorem tg_tr6 : treeOK TGT6 TG6 = true := by quickRfl

end CertificateChecks.KernelJ4Fam
