
module

public import Certificates.Kernel.F4Syl3.RelChk
public import CFSG.Certificates.Kernel.F4Syl3.RelSound
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Elts

public section

namespace CFSG.KC.F4Syl3

open CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.RankThree.PartTwo.Sec21.FF81.F4
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes)

noncomputable abbrev g4E : F42C := evalG (ZMod 2) (wordOfCodes (decW8 CFSG.KD.F4Syl3.w4 CFSG.KD.F4Syl3.l4))

noncomputable abbrev g5E : F42C := evalG (ZMod 2) (wordOfCodes (decW8 CFSG.KD.F4Syl3.w5 CFSG.KD.F4Syl3.l5))

theorem hasBitsS_sE (i : Fin 4) : HasBitsS (ZMod 2) (sE i) (saltOf (sBits i)) :=
  hasBitsS_saltOf (hasBits_sE i)

theorem pres_F42 : Pres sE g4E g5E := by
  refine pres_of_relB (S := [saltOf (sBits 0), saltOf (sBits 1), saltOf (sBits 2),
    saltOf (sBits 3)]) (fun i => ?_) (hasBitsS_wordS _ _) (hasBitsS_wordS _ _)
    (relB_of_relN CFSG.KD.F4Syl3.rel_ok)
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩
  · simp only [Fin.val_mk, List.getD_cons_zero]
    exact hasBitsS_sE _
  · simp only [Fin.val_mk, Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
    exact hasBitsS_sE _
  · simp only [Fin.val_mk, Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
    exact hasBitsS_sE _
  · simp only [Fin.val_mk, Nat.zero_add, List.getD_cons_succ, List.getD_cons_zero]
    exact hasBitsS_sE _
  · omega

end CFSG.KC.F4Syl3

end
