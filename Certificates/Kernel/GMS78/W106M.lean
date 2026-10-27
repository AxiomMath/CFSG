module

public import Certificates.Kernel.GMS78.NM
public import Certificates.Kernel.GMS78.W
public import Certificates.Data.GMS78RuAsmNA
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Batteries.Tactic.Init

public section

namespace CertificateChecks.KernelGMS78

open CFSG.KC.GMS CFSG.ComponentClassification.GMS78.RuPi7 CFSG.ComponentClassification.GMS78.RuAsm
  CFSG.CosetTable

abbrev relsP2 : List (List Nat) :=
  (relsC ++ relsA ++ relsE).filter fun c => c.all fun x => x != 10 && x != 11

theorem relP2_ok : kRel relsP2 ADC TAU NIMG NIMGI = true := by
  quickRfl

theorem nmR_all : ∀ i < 168, nmR GLL INV TW ADC TAU (gllAt GLL i) = true := by
  intro i hi
  interval_cases i
  exacts [nmR_0, nmR_1, nmR_2, nmR_3, nmR_4, nmR_5, nmR_6, nmR_7, nmR_8, nmR_9, nmR_10, nmR_11, nmR_12, nmR_13, nmR_14, nmR_15, nmR_16, nmR_17, nmR_18, nmR_19, nmR_20, nmR_21, nmR_22, nmR_23, nmR_24, nmR_25, nmR_26, nmR_27, nmR_28, nmR_29, nmR_30, nmR_31, nmR_32, nmR_33, nmR_34, nmR_35, nmR_36, nmR_37, nmR_38, nmR_39, nmR_40, nmR_41, nmR_42, nmR_43, nmR_44, nmR_45, nmR_46, nmR_47, nmR_48, nmR_49, nmR_50, nmR_51, nmR_52, nmR_53, nmR_54, nmR_55, nmR_56, nmR_57, nmR_58, nmR_59, nmR_60, nmR_61, nmR_62, nmR_63, nmR_64, nmR_65, nmR_66, nmR_67, nmR_68, nmR_69, nmR_70, nmR_71, nmR_72, nmR_73, nmR_74, nmR_75, nmR_76, nmR_77, nmR_78, nmR_79, nmR_80, nmR_81, nmR_82, nmR_83, nmR_84, nmR_85, nmR_86, nmR_87, nmR_88, nmR_89, nmR_90, nmR_91, nmR_92, nmR_93, nmR_94, nmR_95, nmR_96, nmR_97, nmR_98, nmR_99, nmR_100, nmR_101, nmR_102, nmR_103, nmR_104, nmR_105, nmR_106, nmR_107, nmR_108, nmR_109, nmR_110, nmR_111, nmR_112, nmR_113, nmR_114, nmR_115, nmR_116, nmR_117, nmR_118, nmR_119, nmR_120, nmR_121, nmR_122, nmR_123, nmR_124, nmR_125, nmR_126, nmR_127, nmR_128, nmR_129, nmR_130, nmR_131, nmR_132, nmR_133, nmR_134, nmR_135, nmR_136, nmR_137, nmR_138, nmR_139, nmR_140, nmR_141, nmR_142, nmR_143, nmR_144, nmR_145, nmR_146, nmR_147, nmR_148, nmR_149, nmR_150, nmR_151, nmR_152, nmR_153, nmR_154, nmR_155, nmR_156, nmR_157, nmR_158, nmR_159, nmR_160, nmR_161, nmR_162, nmR_163, nmR_164, nmR_165, nmR_166, nmR_167]

theorem nRelP2 : ∀ c ∈ relsP2, CFSG.GMS78RuN.nEvalW (wordOfCodes 7 c) = CFSG.GMS78RuN.nOneT := by
  have h := (nm_sound _ _ _ _ _ _ _ _ _ _ _ _ _ bindNC_ok inv_ok gll_ok bindTW_ok bindImg_ok rT_ok
    zero_ok nmR_all id_ok faith_ok img_ok relP2_ok clo_ok a0_ok).2.2.2.2.2.1
  intro c hc
  have h' := List.all_eq_true.1 h c hc
  exact beq_iff_eq.1 h'

theorem code_lt {c : List Nat} (hc : c ∈ relsC ++ relsA ++ relsE) : ∀ x ∈ c, x < 14 := by
  intro x hx
  have key : ∀ {R : List (List (Nat × Bool))} {rs : List (List Nat)},
      CFSG.KC.Ord.relsBounded R 9 = true → CFSG.KC.GMSW.relsEqK R (CFSG.KC.GMSW.mkCodesK rs) = true →
        c ∈ rs → x < 14 := by
    intro R rs hb hR hc'
    have hmem : c.map CFSG.KC.GMSW.codeLetK ∈ R := by
      rw [CFSG.KC.GMSW.relsEqK_eq hR, CFSG.KC.GMSW.mkCodesK_eq]
      exact List.mem_map_of_mem hc'
    exact (CFSG.KC.GMSW.codeLetK_of_ne (W.ne_bad hb hmem (List.mem_map_of_mem hx))).1
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · exact key W.RC_bd W.RC_bind hc
    · exact key W.RA_bd W.RA_bind hc
  · exact key W.RE_bd W.RE_bind hc

theorem five_not_mem : (⟨5, by decide⟩ : Fin 7) ∉ ruSub2 := by decide

theorem ruNACheckModel_ok : ruNACheckModel = true := by
  unfold ruNACheckModel
  rw [List.all_eq_true]
  intro r hr
  cases hs : (renumber ruSub2 r).isNone
  · obtain ⟨w', hw'⟩ : ∃ w', renumber ruSub2 r = some w' := by
      cases h : renumber ruSub2 r with
      | none => rw [h] at hs; exact absurd hs (by decide)
      | some w' => exact ⟨w', rfl⟩
    have hlet := map_renumber ruSub2 r w' hw'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
    have hall : (c.all fun x => x != 10 && x != 11) = true := by
      rw [List.all_eq_true]
      intro x hx
      have hx14 := code_lt hc x hx
      have hmem : ((⟨x / 2, by omega⟩ : Fin 7), x % 2 == 0) ∈ wordOfCodes 7 c :=
        List.mem_flatMap.2 ⟨x, hx, List.mem_map.2 ⟨⟨x / 2, by omega⟩,
          List.mem_filter.2 ⟨List.mem_finRange _, by simp⟩, rfl⟩⟩
      rw [← hlet] at hmem
      obtain ⟨l, -, hl⟩ := List.mem_map.1 hmem
      have hS : (⟨x / 2, by omega⟩ : Fin 7) ∈ ruSub2 := by
        have e : ruSub2.get l.1 = ⟨x / 2, by omega⟩ := congrArg Prod.fst hl
        rw [← e]
        exact List.get_mem _ _
      by_contra hne
      have h5 : x / 2 = 5 := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and_or, not_not] at hne
        omega
      exact five_not_mem (by simpa [h5] using hS)
    have hP : c ∈ relsP2 := List.mem_filter.2 ⟨hc, hall⟩
    simp [nRelP2 c hP]
  · rfl

end CertificateChecks.KernelGMS78

end
