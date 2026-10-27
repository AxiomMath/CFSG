module

public import Certificates.Data.HuppertReeEight.Checker
public import Certificates.Kernel.TitsW.Alg
import CFSG.Certificates.Kernel.Spor.PinvSSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW.P188009

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
open HuppertReeEight CertificateChecks.KernelTitsW

syntax "hr_disch" : tactic

theorem Gd_wordL (L : List (List Int)) (wd : List Int) :
    Gd (wordK 1755 11 (mask 11) (pidn 1755 11) (fun j => WG (L.getD j []))
      (fun j => pv (WG (L.getD j []))) wd) :=
  Gd_word (fun _ => Gd_WG _) (fun _ => (Gd_WG _).inv) wd

macro_rules
  | `(tactic| hr_disch) => `(tactic| first
      | (simp (maxDischargeDepth := 64) only [Gd.mul, Gd.inv, Gd.one, Gd_WG, Gd_GS, Gd.pow, Gd_wordL]; done)
      | decide)

theorem aArr_G {w : List Int} (h : lettersK 4 w = true) : aArr w = unpack 1755 11 (WG w) :=
  wordArr_G h

theorem wordArr_listA {L : List (List Int)} (hL : L.all (lettersK 4) = true) {wd : List Int}
    (hl : lettersK L.length wd = true) :
    wordArr 1755 (L.map aArr).toArray wd = unpack 1755 11 (wordK 1755 11 (mask 11) (pidn 1755 11)
      (fun j => WG (L.getD j [])) (fun j => pv (WG (L.getD j []))) wd) := by
  refine wordArr_pk ⟨by simp, fun j hj => ?_⟩ ?_ hl
  · have hj' : j < L.length := hj
    rw [getElem!_pos _ j (by simpa using hj'), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hj']
    exact aArr_G (List.all_eq_true.1 hL _ (List.getElem_mem hj'))
  · exact CFSG.KS.Raw.Orb.allN_iff.2 fun j _ =>
      CFSG.KS.PinvS.permOK_pinvS (Gd_WG _).1 (Gd_WG _).2

theorem syl_eq : sylArrs () = sylWords.map fun w => unpack 1755 11 (WG w) := by
  have h : sylWords.all (lettersK 4) = true := by quickRfl
  unfold sylArrs
  apply List.map_congr_left
  intro w hw
  exact aArr_G (List.all_eq_true.1 h w hw)

theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

theorem sylow : sylowCheck () = true := by
  unfold sylowCheck
  simp (disch := hr_disch) only [syl_eq, List.all_map, List.any_map, List.pairwise_map,
    Function.comp_def, cubeE, memE, compA_G, eqA_G, idA_G]
  quickRfl

theorem cover : coverCheck () = true := by
  unfold coverCheck
  simp (disch := hr_disch) only [syl_eq, planeData, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, aArr_G, isPairE,
    oneE, cubeE, commE, memE, powsE, planeE, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.filter_map, List.all_map, List.any_map,
    Function.comp_def, compA_G, eqA_G, idA_G]
  quickRfl

theorem gen : genCheck () = true := by
  unfold genCheck
  simp only [planeData, List.all_cons, List.all_nil, Bool.and_true, genCheckAt, range4]
  simp (disch := hr_disch) only [wordArr_listA, gen_get]
  simp (disch := hr_disch) only [cenZ, cenV, slp, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, aArr_G, commE, compA_G, eqA_G, invCand_G, isInvA_G, idA_G]
  quickRfl

end CertificateChecks.KernelTitsW.P188009

end
