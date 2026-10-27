module

public import Certificates.Kernel.LocalComp.E8Tables
public import Certificates.Kernel.LocalComp.Weyl3184Facts
public import CFSG.Certificates.Kernel.LocalCompE8CentSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCentData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylD8Data
public import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3220

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight
open CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelLC.W3184 (strictB_eq bindList_spec map_get unpack_get)

@[expose] noncomputable def DW : Nat := nat_lit 6215229778066649957086350410782548311986439129836723789740714223843222383020292464404908892795966916407934058744201513869204088935325712202947518720978332358166442021088835157980262530088145103271471879738045832945259680472213073982007774400697154064515992624697183244

@[expose] noncomputable def SW : Nat := nat_lit 94966769309714337273215386336809542559157857407470207132750371393065255906766019131218892012120882127183617884803543350746449466137909545676513409153489722284390020917206363703359666714380413971518711918139554454474812508332167795455759584247085527820714034380002446418511035769880951786760029153739466731551962438385032901676144411938219964214225975460896447495342384682027740370817411519672635196894186841553569920837645493332481467478824216723492515756054771039485134376924838699686056981963857915193575722444100010609358788903723268172891857971991577089187045135990013296640

@[expose] noncomputable def FW : Nat := nat_lit 1257668486286519883718829325418882

@[expose] noncomputable def KP : Nat := nat_lit 7812998068708900865

theorem kD : dFixK E8.ST DW = true := by quickRfl
theorem kS : sOrbK E8.ST SW = true := by quickRfl
theorem kF : frameReflK E8.RT KP FW = true := by quickRfl
theorem kKP : bindList keyPts 8 KP = true := by quickRfl
theorem kW : wt2K E8.ST = true := by quickRfl
theorem kT : tripleK = true := by quickRfl
theorem kP : pair2K = true := by quickRfl

theorem signArrs_get (m : Nat) (hm : m < 256) (he : framePop m % 2 = 0) :
    signArrs[m]! = unpack 240 8 (E8.ST m) := by
  rw [← E8.sign_eq m hm he, signArrs, map_get _ _ m (by simpa using hm),
    getElem!_pos _ m (by simpa using hm), List.getElem_range]

theorem reflArrs_get (r : Nat) (hr : r < 240) : reflArrs[r]! = unpack 240 8 (E8.RT r) := by
  rw [← E8.refl_eq r hr, reflArrs, map_get _ _ r (by simpa using hr),
    getElem!_pos _ r (by simpa using hr), List.getElem_range]

theorem even_of (m : Nat) (h : Nat.beq (Nat.land (pop8 m) 1) 0 = true) : framePop m % 2 = 0 := by
  rw [← pop8_eq]
  have h1 : pop8 m &&& 1 = 0 := Nat.eq_of_beq_eq_true h
  rwa [Nat.and_one_is_mod] at h1

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3220 : (dFixCheck = true)
    ∧ (sOrbitCheck = true)
    ∧ (frameReflCheck = true)
    ∧ (wt2FixCheck = true)
    ∧ (tripleCheck = true)
    ∧ (pairCheck2 = true) := by
  refine ⟨?_, ?_, ?_, ?_, tripleK_sound kT, pair2K_sound kP⟩
  · simp only [dFixCheck, allLt_iff, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq]
    intro r hr
    have k := allN_spec kD r hr
    simp only [dFixAt, bAnd_iff, Nat.blt_eq] at k
    obtain ⟨k1, k2, k3, k4⟩ := k
    refine ⟨_, k1, ⟨⟨even_of _ k2, by omega⟩, ?_⟩⟩
    rw [signArrs_get _ k1 (even_of _ k2), unpack_get (by omega)]
    exact Nat.eq_of_beq_eq_true k4
  · simp only [sOrbitCheck, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
    intro r hr
    by_cases h112 : r < 112
    · exact Or.inl h112
    · right
      have k := allN_spec kS r hr
      have hb : Nat.blt r 112 = false :=
        Bool.eq_false_iff.2 (fun h => h112 (by simpa [Nat.blt_eq] using h))
      have k' : sOrbAt E8.ST r (pg 8 255 SW r) = true := by
        rw [hb] at k
        exact k
      simp only [sOrbAt, bAnd_iff, Nat.blt_eq] at k'
      obtain ⟨k1, k2, k3⟩ := k'
      refine ⟨_, k1, even_of _ k2, ?_⟩
      rw [signArrs_get _ k1 (even_of _ k2), unpack_get (by omega)]
      exact Nat.eq_of_beq_eq_true k3
  · simp only [frameReflCheck, allLt_iff, List.any_eq_true, List.mem_range, beq_iff_eq]
    intro i hi
    have k := allN_spec kF i hi
    simp only [frameAt, bAnd_iff, Nat.blt_eq] at k
    obtain ⟨k1, k2⟩ := k
    obtain ⟨hlen, hkp⟩ := bindList_spec kKP
    set w := pg 14 16383 FW i
    have ha : Nat.land w 127 < 128 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
    have hb : Nat.shiftRight w 7 < 128 := by
      change w >>> 7 < 128
      rw [Nat.shiftRight_eq_div_pow]
      omega
    have k2' := Nat.eq_of_beq_eq_true k2
    simp only [Nat.add_eq] at k2'
    refine ⟨Nat.land w 127, ha, Nat.shiftRight w 7, hb, ?_⟩
    rw [reflArrs_get _ (by omega), unpack_get (by omega)]
    change pg 8 255 (E8.RT (112 + w.land 127)) (112 + w.shiftRight 7) = _
    rw [k2', ← (hkp i hi).2, List.getD_eq_getElem _ _ (by omega), getElem!_pos keyPts i (by omega)]
  · simp only [wt2FixCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq, beq_iff_eq]
    intro m hm
    have k := allN_spec kW m hm
    by_cases he : framePop m % 2 = 0
    · by_cases h0 : m = 0
      · exact Or.inl (Or.inr h0)
      · right
        have hev : Nat.beq (Nat.land (pop8 m) 1) 0 = true := by
          have h1 : pop8 m &&& 1 = 0 := by rw [Nat.and_one_is_mod, pop8_eq]; exact he
          exact Nat.beq_eq_true_eq _ _ ▸ h1
        rw [hev] at k
        have h0' : Nat.beq m 0 = false :=
          Bool.eq_false_iff.2 (fun h => h0 (Nat.eq_of_beq_eq_true h))
        rw [h0'] at k
        rw [signArrs_get m hm he, fixCntK_sound, ← pop8_eq]
        cases h60 : Nat.beq (fixCntK 240 8 (E8.ST m)) 60 <;> cases h2 : Nat.beq (pop8 m) 2
        · rw [beq_eq_false_iff_ne.2 (Nat.ne_of_beq_eq_false h60),
            beq_eq_false_iff_ne.2 (Nat.ne_of_beq_eq_false h2)]
        all_goals simp_all [notB', Nat.beq_eq]
    · exact Or.inl (Or.inl he)

end CertificateChecks.KernelLC.W3220

end
