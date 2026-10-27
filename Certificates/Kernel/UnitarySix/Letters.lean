
module

public import Certificates.Kernel.UnitarySix.LettersBase

public import Certificates.Kernel.UnitarySix.Gen
public import CFSG.Certificates.Kernel.U6Sound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
public import Certificates.Kernel.UnitarySix.GenEq
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.KLie.CT

theorem letters_eq :
    LetsBind CFSG.EvenSmallLie.UnitarySix.u62Letters U.LT := by
  have hs := letters_sound up_eq pos_eq tv_eq kLet
  refine ⟨by simp [CFSG.EvenSmallLie.UnitarySix.u62Letters], fun k hk p => ?_⟩
  have hget : CFSG.EvenSmallLie.UnitarySix.u62Letters.getD k 1 =
      CFSG.EvenSmallLie.UnitarySix.letter k hk := by
    simp [CFSG.EvenSmallLie.UnitarySix.u62Letters, List.getD_eq_getElem?_getD, hk]
  rw [hget, CFSG.EvenSmallLie.UnitarySix.letter, CFSG.Sporadic.Schreier.tab_eq]
  change CFSG.Sporadic.Th.Native.ap (CFSG.EvenSmallLie.UnitarySix.letterT k) p.val % 693 = _
  rw [letterT_eq, natAbs_succ_sub]
  obtain ⟨-, -, hp⟩ := hs k hk
  rw [(hp p.val p.2).1, Nat.mod_eq_of_lt (hp p.val p.2).2]

end CertificateChecks.KernelU6

end
