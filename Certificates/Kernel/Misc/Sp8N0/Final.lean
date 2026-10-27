module

public import CFSG.Certificates.Kernel.Misc.Sp8N0Sound
public import Certificates.Kernel.Misc.Sp8N0.Checks
public import Certificates.Kernel.Misc.Sp8Syl3.Final

public section

namespace CFSG.KD.Sp8N0

open CFSG.KC.Sp8N0 CFSG.KC.Sp8Syl3 CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

theorem n04_header : Header REC where
  gens := by decide +kernel
  zs := by decide +kernel
  zz := by decide +kernel
  z012 := by decide +kernel
  z0123 := by decide +kernel
  e2 := by decide +kernel
  invs := by decide +kernel

theorem cert899104_ok : n0Chk899104 = true ∧ fixChk899104 = true ∧ clsChk899104 = true ∧
    normChk899104 = true ∧ prodChk899104 = true :=
  ⟨n0Chk_of n04_header CFSG.KD.Sp8Syl3.sy3_gens CFSG.KD.Sp8Syl3.sy3_tabE_ok n04_tab_ok n04_mem_ok
      n04_conj_ok,
    n04_fix_ok,
    clsChk_of n04_header CFSG.KD.Sp8Syl3.sy3_gens CFSG.KD.Sp8Syl3.sy3_tabE_ok n04_tab_ok
      n04_cls_ok,
    normChk_of n04_header n04_tab_ok n04_norm_ok,
    prodChk_of n04_header n04_tab_ok n04_prod_ok⟩

end CFSG.KD.Sp8N0

end
