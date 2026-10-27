module

public import CFSG.Quasithin.Vol2.KGFactE64M24KInputs
public import Certificates.Kernel.M24Dc.E64C0
public import Certificates.Kernel.M24Dc.E64C1
public import Certificates.Kernel.M24Dc.E64C2
public import Certificates.Kernel.M24Dc.E64C3
public import Certificates.Kernel.M24Dc.Final
public import CFSG.Certificates.Kernel.E64LEq
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Dc

public section

namespace CFSG.KD.M24Dc

open CFSG.KC.SLDc CFSG.KC.E64L CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.KGE64
open CFSG.QuasithinUnique.Ch1.SporLat.M24 CFSG.QuasithinUnique.Ch1.SporLat.M24K

theorem ltL_eq (j : Nat) : (mLet j).toList.map Array.toList = ltL j := by
  simp [mLet, sT, T, ltL, wordTabL, wordTabT, wordImg_eqT]

theorem e64M_ok : ∀ i < 4, e64M i = true
  | 0, _ => E64C0.c0
  | 1, _ => E64C1.c0
  | 2, _ => E64C2.c0
  | 3, _ => E64C3.c0
  | _ + 4, h => absurd h (by omega)

theorem e64_member {i : Nat} (hi : i < 4) :
    e64Check 24 (List.range 24) (codeSetAct 24)
      (m24LatK.sTabs ++ m24LatK.mt[e64J i]!).toArray (e64Y i) (e64O i)
      m24LatK.Om[e64J i]!.lbl.toList = true := by
  have hj : e64J i < 13 := by interval_cases i <;> decide
  rw [mLet_eq facts hj, Om_get hj, codeSetAct_eq, e64Check_eqT _ _ _ (codeSetTL 24)
    (codeSetT_eqT 24), ltL_eq]
  exact e64M_ok i hi

theorem e64K : m24E64K :=
  ⟨e64_member (i := 0) (by decide), e64_member (i := 1) (by decide),
    e64_member (i := 2) (by decide), e64_member (i := 3) (by decide)⟩

end CFSG.KD.M24Dc

end
