module

public import Certificates.Kernel.GMS78.W107Chk
public import Certificates.Kernel.GMS78.Coset.XGRuP12
public import CFSG.Certificates.Kernel.GMS78RuCzmSound
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.KC.GMS CFSG.ComponentClassification.GMS78.RuCz
  CFSG.ComponentClassification.GMS78.RuAsm

theorem p12_eq : p12Rels.map encW = CFSG.KBRoute.XGRuP12.rels := by rfl

theorem wp12_eq : CFSG.KBRoute.XGRuP12.T1.words =
    (subsetOf 9 [0, 1, 2, 3, 4, 5]).map fun x => [(x.val, true)] := by rfl

theorem czm_index : (genSub {r | r ∈ p12Rels.map FreeGroup.mk}
      (subsetOf sub9.length [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r | r ∈ p12Rels.map FreeGroup.mk} (subsetOf sub9.length [0, 1, 2, 3, 4, 5])).index ≤
      24 := by
  have t := CertificateChecks.KernelMiscCoset.XGRuP12.t1
  unfold CFSG.KBRoute.XGRuP12.T1.ok at t
  exact genSub_index_le_of_tableOk _ p12_eq t (by decide) CFSG.KBRoute.XGRuP12.top _ wp12_eq

theorem nMulT_eq (p q) : CFSG.GMS78RuN.nMulT p q = Gen.nMulT CFSG.GMS78RuN.nBetaTab
    CFSG.GMS78RuN.nTwTab CFSG.GMS78RuN.nCols CFSG.GMS78RuN.nBasis p q := rfl

theorem nEvalW_eq (w) : CFSG.GMS78RuN.nEvalW w = Gen.nEvalW CFSG.GMS78RuN.nBetaTab
    CFSG.GMS78RuN.nTwTab CFSG.GMS78RuN.nCols CFSG.GMS78RuN.nBasis CFSG.GMS78RuN.nImg
    CFSG.GMS78RuN.nImgInv w := rfl

theorem czmZ0_eq : czmZ0Check = Gen.czmZ0CheckG CFSG.GMS78RuN.nBetaTab CFSG.GMS78RuN.nTwTab
    CFSG.GMS78RuN.nCols CFSG.GMS78RuN.nBasis CFSG.GMS78RuN.nImg CFSG.GMS78RuN.nImgInv ruZ0Word := by
  rw [czmZ0Check, Gen.czmZ0CheckG, nEvalW_eq]

theorem czmLetter_eq : czmLetterCheck = Gen.czmLetterCheckG CFSG.GMS78RuN.nBetaTab
    CFSG.GMS78RuN.nTwTab CFSG.GMS78RuN.nCols CFSG.GMS78RuN.nBasis CFSG.GMS78RuN.nImg
    CFSG.GMS78RuN.nImgInv := by
  simp only [czmLetterCheck, Gen.czmLetterCheckG, czmConj, Gen.czmConjG, nMulT_eq]

theorem czmJ_eq : czmJCheck = Gen.czmJCheckG CFSG.GMS78RuN.nBetaTab CFSG.GMS78RuN.nTwTab
    CFSG.GMS78RuN.nCols CFSG.GMS78RuN.nBasis CFSG.GMS78RuN.nImg CFSG.GMS78RuN.nImgInv czmJWord := by
  simp only [czmJCheck, Gen.czmJCheckG, czmSame, Gen.czmSameG, czmConjW, Gen.czmConjWG, czmConj,
    Gen.czmConjG, nMulT_eq, nEvalW_eq]

theorem czmRep_eq : czmRepCheck = Gen.czmRepCheckG CFSG.GMS78RuN.nBetaTab CFSG.GMS78RuN.nTwTab
    CFSG.GMS78RuN.nCols CFSG.GMS78RuN.nBasis CFSG.GMS78RuN.nImg CFSG.GMS78RuN.nImgInv czmRep := by
  simp only [czmRepCheck, Gen.czmRepCheckG, czmSame, Gen.czmSameG, czmConjW, Gen.czmConjWG, czmConj,
    Gen.czmConjG, nMulT_eq, nEvalW_eq]

theorem nmR_all' : ∀ i < 168, nmR GLL INV TW ADC TAU (gllAt GLL i) = true := by
  intro i hi
  interval_cases i
  exacts [nmR_0, nmR_1, nmR_2, nmR_3, nmR_4, nmR_5, nmR_6, nmR_7, nmR_8, nmR_9, nmR_10, nmR_11,
    nmR_12, nmR_13, nmR_14, nmR_15, nmR_16, nmR_17, nmR_18, nmR_19, nmR_20, nmR_21, nmR_22, nmR_23,
    nmR_24, nmR_25, nmR_26, nmR_27, nmR_28, nmR_29, nmR_30, nmR_31, nmR_32, nmR_33, nmR_34, nmR_35,
    nmR_36, nmR_37, nmR_38, nmR_39, nmR_40, nmR_41, nmR_42, nmR_43, nmR_44, nmR_45, nmR_46, nmR_47,
    nmR_48, nmR_49, nmR_50, nmR_51, nmR_52, nmR_53, nmR_54, nmR_55, nmR_56, nmR_57, nmR_58, nmR_59,
    nmR_60, nmR_61, nmR_62, nmR_63, nmR_64, nmR_65, nmR_66, nmR_67, nmR_68, nmR_69, nmR_70, nmR_71,
    nmR_72, nmR_73, nmR_74, nmR_75, nmR_76, nmR_77, nmR_78, nmR_79, nmR_80, nmR_81, nmR_82, nmR_83,
    nmR_84, nmR_85, nmR_86, nmR_87, nmR_88, nmR_89, nmR_90, nmR_91, nmR_92, nmR_93, nmR_94, nmR_95,
    nmR_96, nmR_97, nmR_98, nmR_99, nmR_100, nmR_101, nmR_102, nmR_103, nmR_104, nmR_105, nmR_106,
    nmR_107, nmR_108, nmR_109, nmR_110, nmR_111, nmR_112, nmR_113, nmR_114, nmR_115, nmR_116,
    nmR_117, nmR_118, nmR_119, nmR_120, nmR_121, nmR_122, nmR_123, nmR_124, nmR_125, nmR_126,
    nmR_127, nmR_128, nmR_129, nmR_130, nmR_131, nmR_132, nmR_133, nmR_134, nmR_135, nmR_136,
    nmR_137, nmR_138, nmR_139, nmR_140, nmR_141, nmR_142, nmR_143, nmR_144, nmR_145, nmR_146,
    nmR_147, nmR_148, nmR_149, nmR_150, nmR_151, nmR_152, nmR_153, nmR_154, nmR_155, nmR_156,
    nmR_157, nmR_158, nmR_159, nmR_160, nmR_161, nmR_162, nmR_163, nmR_164, nmR_165, nmR_166,
    nmR_167]

theorem czmInvol_eq : czmInvolCheck = Gen.czmInvolCheckG CFSG.GMS78RuSim.glList := rfl

theorem glOK_glList : Gen.glOK CFSG.GMS78RuSim.glList = true := by quickRfl

open CFSG.ComponentClassification.GMS78 in
theorem certificate107 : ((CFSG.CosetTable.genSub {r | r ∈ RuCz.p12Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf RuCz.sub9.length [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (CFSG.CosetTable.genSub {r | r ∈ RuCz.p12Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf RuCz.sub9.length [0, 1, 2, 3, 4, 5])).index ≤ 24) ∧
    RuCz.czmZ0Check = true ∧ RuCz.czmLetterCheck = true ∧
    RuCz.czmJCheck = true ∧ RuCz.czmRepCheck = true ∧ RuCz.czmInvolCheck = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := czm_sound _ _ _ _ CFSG.GMS78RuS.sBasis _ _ _ _ ruZ0Word czmJWord
    czmRep CFSG.GMS78RuSim.glList bindNC_ok inv_ok gll_ok bindTW_ok bindImg_ok zero_ok nmR_all'
    id_ok img_ok xp_ok z0p_ok kz0_ok kletter_ok kj_ok krep_ok kinvol_ok glOK_glList
  exact ⟨czm_index, czmZ0_eq ▸ h1, czmLetter_eq ▸ h2, czmJ_eq ▸ h3, czmRep_eq ▸ h4,
    czmInvol_eq ▸ h5⟩

end CertificateChecks.KernelGMS78

end
