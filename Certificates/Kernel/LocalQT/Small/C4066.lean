module

public import Certificates.Kernel.Misc.Perm.HSMcL
public import CFSG.Certificates.Kernel.LocalQTA6Sound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public meta import CFSG.Sporadic.Schreier.PairHSCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSClass

set_option maxRecDepth 400000

public section

namespace CFSG.KD.LQT.C4066

meta def a0M : Array Nat := CFSG.Sporadic.Schreier.PairHS.gens[0]!

meta def a1M : Array Nat := CFSG.Sporadic.Schreier.PairHS.gens[1]!

meta def a1iM : Array Nat := CFSG.Sporadic.Schreier.PairHS.gensInv[1]!

end CFSG.KD.LQT.C4066

#ks_perm CFSG.KD.LQT.C4066.A0 12 CFSG.KD.LQT.C4066.a0M

#ks_perm CFSG.KD.LQT.C4066.A1 12 CFSG.KD.LQT.C4066.a1M

#ks_perm CFSG.KD.LQT.C4066.A1i 12 CFSG.KD.LQT.C4066.a1iM

namespace CFSG.KD.LQT.C4066

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.A6
open CFSG.Sporadic.Schreier CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.QuasithinUnique.Id2519.UHS CertificateChecks.KernelMisc.HSMcL

theorem e0 : Nat.beq (HS.F 0) A0 = true := by quickRfl
theorem e1 : Nat.beq (HS.F 1) A1 = true := by quickRfl
theorem i1 : invEqK 3850 12 (mask 12) (3850 * 12) A1 A1i = true := by quickRfl

theorem k : a6K A0 A1 A1i y1Letters y2Letters cLetters nodePar.toList nodeLab.toList
    conjWords.toList = true := by quickRfl

theorem g0_eq : PairHS.gens[0]! = unpack 3850 12 A0 := by
  rw [← Nat.eq_of_beq_eq_true e0, ← hsStrongArrs_get 0 (by norm_num)]
  simp only [PairHS.gens, List.getElem!_toArray, List.getElem!_cons_zero]

theorem g1_eq : PairHS.gens[1]! = unpack 3850 12 A1 := by
  rw [← Nat.eq_of_beq_eq_true e1, ← hsStrongArrs_get 1 (by norm_num)]
  simp only [PairHS.gens, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem g1i_eq : PairHS.gensInv[1]! = unpack 3850 12 A1i := by
  have hs : 1 < hsStrongArrs.size := by
    unfold hsStrongArrs
    simp
  have h : PairHS.gensInv[1]! = invCand 3850 hsStrongArrs[1]! := by
    simp only [PairHS.gensInv, List.getElem!_toArray, List.getElem!_cons_succ,
      List.getElem!_cons_zero]
    rw [rawInvs, getElem!_pos _ 1 (by simpa using hs), Array.getElem_map, getElem!_pos _ 1 hs]
  rw [h, hsStrongArrs_get 1 (by norm_num), Nat.eq_of_beq_eq_true e1]
  exact (invEqK_sound i1).1

theorem facts : a6Check = true := by
  rw [a6Check_eq]
  exact a6_sound g0_eq g1_eq g1i_eq _ _ _ _ _ _ _ nodeWord_eq k

end CFSG.KD.LQT.C4066

end
