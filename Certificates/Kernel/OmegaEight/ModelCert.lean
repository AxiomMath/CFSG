module

public import CFSG.Certificates.Kernel.O8ModelBasicSound
public import CFSG.Certificates.Kernel.O8ModelOSetSound
public import CFSG.Certificates.Kernel.O8ModelS5Sound
public import CFSG.Certificates.Kernel.O8ModelQ3Sound
public import Certificates.Kernel.OmegaEight.ModelChecks
public import Certificates.Kernel.OmegaEight.ModelS5ElemP
public import Certificates.Kernel.OmegaEight.ModelS5ElemM
public import Certificates.Kernel.OmegaEight.ModelS5ClsP
public import Certificates.Kernel.OmegaEight.ModelS5ClsM
public import Certificates.Kernel.OmegaEight.ModelS5Adj
public import Certificates.Kernel.OmegaEight.ModelS5Enum
public import Certificates.Kernel.OmegaEight.ModelLetters
public import Certificates.Kernel.OmegaEight.CPM
public import Certificates.Kernel.OmegaEight.Til
public import Certificates.Kernel.LocalComp.Weyl3185

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelLC.W3185
open CFSG.KC.Enum (pidn permOK pg)

theorem bindsPP : Binds 120 9 PP.S 20 6 PP.BP (pS .plus) (pBaseA .plus) := by
  obtain ⟨hs, he⟩ := pushWords_eq pOP_bind PP.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem bindsPM : Binds 136 8 PM.S 18 6 PM.BP (pS .minus) (pBaseA .minus) := by
  obtain ⟨hs, he⟩ := pushWords_eq pOM_bind PM.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem levelsPP : LevelsK 120 9 PP.S PP.SI PP.LR PP.TR PP.TRI 20 12 6 PP.BP pWordsP (pS .plus)
    (pBaseA .plus) := ⟨bindsPP, PP.head, PP.hl⟩

theorem levelsPM : LevelsK 136 8 PM.S PM.SI PM.LR PM.TR PM.TRI 18 12 6 PM.BP pWordsM (pS .minus)
    (pBaseA .minus) := ⟨bindsPM, PM.head, PM.hl⟩

theorem levelsLp : LevelsK 120 9 Om1.S Om1.SI Om1.LR Om1.TR Om1.TRI 17 8 7 Om1.BP
    OmegaEight.omegaWords (lS .plus) (lBaseA .plus) := ⟨binds1, Om1.head, Om1.hl⟩

theorem chainP : chainCheck .plus = true := by
  have h1 : rawChainOK 120 ((pS .plus).extract 0 12) (pS .plus) (pBaseA .plus)
      (OmegaEight.wordsOf 12 (pWords .plus)) 4 = true := by
    rw [wordsOf_eq]
    exact rawChainK_sound bindsPP PP.head PP.hl (by decide) PP.hs
  have h2 : rawOrbitSizes 120 (pS .plus) (pBaseA .plus) = pSizes .plus := by
    rw [rawOrbitSizesK_sound bindsPP permsPP PP.hl]
    decide +kernel
  have h3 : rawChainOK 120 ((uS .plus).extract 0 12) (uS .plus) (uBaseA .plus)
      (OmegaEight.wordsOf 12 []) 4 = true := by
    rw [wordsOf_eq]
    exact rawChainK_sound levelsUP.1 UP.head UP.hl (by decide) UP.hs
  have h4 : rawOrbitSizes 120 (uS .plus) (uBaseA .plus) = uSizes .plus := by
    rw [rawOrbitSizesK_sound levelsUP.1 permsUP UP.hl]
    decide +kernel
  simp only [Model.chainCheck, Model.deg, h1, h2, h3, h4, beq_self_eq_true, Bool.and_self]

theorem chainM : chainCheck .minus = true := by
  have h1 : rawChainOK 136 ((pS .minus).extract 0 12) (pS .minus) (pBaseA .minus)
      (OmegaEight.wordsOf 12 (pWords .minus)) 4 = true := by
    rw [wordsOf_eq]
    exact rawChainK_sound bindsPM PM.head PM.hl (by decide) PM.hs
  have h2 : rawOrbitSizes 136 (pS .minus) (pBaseA .minus) = pSizes .minus := by
    rw [rawOrbitSizesK_sound bindsPM permsPM PM.hl]
    decide +kernel
  have h3 : rawChainOK 136 ((uS .minus).extract 0 12) (uS .minus) (uBaseA .minus)
      (OmegaEight.wordsOf 12 []) 4 = true := by
    rw [wordsOf_eq]
    exact rawChainK_sound levelsUM.1 UM.head UM.hl (by decide) UM.hs
  have h4 : rawOrbitSizes 136 (uS .minus) (uBaseA .minus) = uSizes .minus := by
    rw [rawOrbitSizesK_sound levelsUM.1 permsUM UM.hl]
    decide +kernel
  simp only [Model.chainCheck, Model.deg, h1, h2, h3, h4, beq_self_eq_true, Bool.and_self]

theorem basicCheck_eq (ε : Eps) : basicCheck ε = basicCheckG (deg ε) (psiT ε) (lS ε) (lBaseA ε)
    (pS ε) (pBaseA ε) (uS ε) (uBaseA ε) (pArr ε) (uArr ε) (genRows ε)
    (CFSG.EvenSmallLie.OmegaEight.Stage2.urRows ε) := by
  cases ε <;> rfl

theorem psiT_eq (ε : Eps) {y : ℕ} (hy : y < 64) : psiT ε y = psiArr ε y := by
  cases ε <;> simp [psiT, Model.psiTab, psiTabPlus, psiTabMinus, Array.getD, hy]

theorem pArrP_bind : ∀ i < 6, pArr .plus i = unpack 120 9 (PP.S (6 + i)) := by
  intro i hi
  rw [← pOP_bind.2 (6 + i) (by omega)]
  interval_cases i <;> rfl

theorem pArrM_bind : ∀ i < 6, pArr .minus i = unpack 136 8 (PM.S (6 + i)) := by
  intro i hi
  rw [← pOM_bind.2 (6 + i) (by omega)]
  interval_cases i <;> rfl

theorem urP_bind : ∀ k < 6, CFSG.EvenSmallLie.OmegaEight.Stage2.urRows .plus k =
    decR (mat UPlus k) := by
  intro k hk
  interval_cases k <;> rfl

theorem urM_bind : ∀ k < 6, CFSG.EvenSmallLie.OmegaEight.Stage2.urRows .minus k =
    decR (mat UMinus k) := by
  intro k hk
  interval_cases k <;> rfl

theorem psiTP (y : ℕ) (hy : y < 64) : (psiT .plus y).toList =
    (List.range 120).map fun i => fget (psiK false NSP NIP 120 9 5665569 y) i 9 := by
  rw [psiT_eq .plus hy, psiArrP_eq]
  exact psiP_sound formP kNsP bposP y

theorem psiTM (y : ℕ) (hy : y < 64) : (psiT .minus y).toList =
    (List.range 136).map fun i => fget (psiK true NSM NIM 136 8 4552225 y) i 8 := by
  rw [psiT_eq .minus hy, psiArrM_eq]
  exact psiM_sound formM kNsM bposM y

theorem basicP : basicCheck .plus = true := by
  rw [basicCheck_eq]
  exact basic_sound levelsLp levelsPP levelsUP psiTP pArrP_bind uArrP_bind bindGP urP_bind kBasicP

theorem basicM : basicCheck .minus = true := by
  rw [basicCheck_eq]
  exact basic_sound levelsLm levelsPM levelsUM psiTM pArrM_bind uArrM_bind bindGM urM_bind kBasicM

theorem memU_eq (ε : Eps) : memU ε = memG (deg ε) (uS ε) (uBaseA ε) := by
  funext g
  cases ε <;> rfl

theorem memL_eq (ε : Eps) : memL ε = memG (deg ε) (lS ε) (lBaseA ε) := by
  funext g
  cases ε <;> rfl

theorem oSetCheckW_eq (ε : Eps) (T : Array (Array ℕ)) : oSetCheckW ε T =
    oSetCheckG (deg ε) (psiT ε) (lS ε) (lBaseA ε) (pBaseA ε) (nOrb ε) T := by
  cases ε <;> rfl

theorem r3CheckW_eq (T : Array (Array ℕ)) :
    r3CheckW T = r3CheckG (psiT .plus) (uOrig .plus) T := rfl

theorem adjTabW_eq (ε : Eps) (S : Array (Array ℕ)) (D : UCls) :
    adjTabW ε S D = adjTabG (deg ε) S D := rfl

theorem okPreW_eq (ε : Eps) (S : Array (Array ℕ)) (D : UCls) :
    okPreW ε S D = okPreG (adjTabW ε S D) := rfl

theorem s5CheckW_eq (ε : Eps) (S : Array (Array ℕ)) (D : UCls) : s5CheckW ε S D =
    s5CheckG (deg ε) (uS ε) (uBaseA ε) (lS ε) (lBaseA ε) (psiT ε 1) (cands ε) S D := by
  simp only [s5CheckW, finalOKW, lWord, okPreW_eq, adjTabW_eq, memU_eq, memL_eq, s5CheckG]
  rfl

theorem q3CheckW_eq (F : Array (Array ℕ)) : q3CheckW F =
    q3CheckG (uArr .plus) (uOrig .plus) (pS .plus) (pBaseA .plus) flagA flagB F
      OmegaEight.genArrs[8]! OmegaEight.omegaS uWordsPlus (psiTT .plus) (uS .plus) (uBaseA .plus)
      sigTarget := rfl

@[expose] noncomputable def TP : Array (Array ℕ) :=
  Array.ofFn (n := 135) fun i => unpack 120 9 (perAt 120 9 MdTP i.val)

@[expose] noncomputable def TM : Array (Array ℕ) :=
  Array.ofFn (n := 119) fun i => unpack 136 8 (perAt 136 8 MdTM i.val)

@[expose] noncomputable def FP : Array (Array ℕ) :=
  Array.ofFn (n := 315) fun i => unpack 120 9 (perAt 120 9 MdF i.val)

theorem bindOTP : ListBind 120 9 TP MdTP 135 := by
  refine ⟨by simp [TP], fun i hi => ?_⟩
  rw [getElem!_pos TP i (by simp [TP]; omega)]
  simp [TP]

theorem bindOTM : ListBind 136 8 TM MdTM 119 := by
  refine ⟨by simp [TM], fun i hi => ?_⟩
  rw [getElem!_pos TM i (by simp [TM]; omega)]
  simp [TM]

theorem bindFP : ListBind 120 9 FP MdF 315 := by
  refine ⟨by simp [FP], fun i hi => ?_⟩
  rw [getElem!_pos FP i (by simp [FP]; omega)]
  simp [FP]

theorem unpack_toList {n w P : Nat} :
    (unpack n w P).toList = (List.range n).map fun i => fget P i w := by
  apply List.ext_getElem
  · simp [unpack]
  · intro i h1 h2
    simp [unpack, fget, CFSG.KC.Enum.pg, mask, maskN, pw2, Nat.mul_comm]

theorem eq_unpack {a : Array ℕ} {n w P : Nat}
    (h : a.toList = (List.range n).map fun i => fget P i w) : a = unpack n w P :=
  Array.toList_inj.mp (h.trans unpack_toList.symm)

theorem sigTarget_bind : ∀ j < 6, sigTarget j = unpack 120 9 (TGP j) := by
  intro j hj
  interval_cases j
  · exact eq_unpack (by rw [sigTarget, psiArrP_eq]; exact psiP_sound formP kNsP bposP 1)
  · exact eq_unpack (by rw [sigTarget, psiArrP_eq]; exact psiP_sound formP kNsP bposP 2)
  · exact uArrP_bind 3 (by norm_num)
  · exact eq_unpack (by rw [sigTarget, psiArrP_eq]; exact psiP_sound formP kNsP bposP 4)
  · exact uArrP_bind 4 (by norm_num)
  · exact uArrP_bind 5 (by norm_num)

theorem oSetP : oSetCheckW .plus TP = true := by
  rw [oSetCheckW_eq]
  exact oSet_sound psiTP levelsLp bindsPP.2.2.2.2.2 bindOTP kOSetP

theorem oSetM : oSetCheckW .minus TM = true := by
  rw [oSetCheckW_eq]
  exact oSet_sound psiTM levelsLm bindsPM.2.2.2.2.2 bindOTM kOSetM

theorem r3P : r3CheckW TP = true := by
  rw [r3CheckW_eq]
  exact r3_sound psiTP ⟨levelsUP.1.2.2.2.1, levelsUP.1.2.2.2.2.1⟩ bindOTP (by norm_num) kR3Perm
    kR3P

theorem s5P : s5CheckW .plus (uListK 120 9 ⟨UP.LR, UP.TR, UP.TRI, UP.BP, 5⟩)
    (uClsK MdCLSP MdREPSP MdNCP) = true := by
  rw [s5CheckW_eq]
  exact s5_sound levelsUP levelsLp (psiTP 1 (by norm_num)) kPsiCanP kLettersCP kClsP kS5ElemP
    kS5ClsP kRepP kS5AdjP kSizeP (by rw [kNCP]; decide) kEnumP

theorem s5M : s5CheckW .minus (uListK 136 8 ⟨UM.LR, UM.TR, UM.TRI, UM.BP, 3⟩)
    (uClsK MdCLSM MdREPSM MdNCM) = true := by
  rw [s5CheckW_eq]
  exact s5_sound levelsUM levelsLm (psiTM 1 (by norm_num)) kPsiCanM kLettersCM kClsM kS5ElemM
    kS5ClsM kRepM kS5AdjM kSizeM (by rw [kNCM]; decide) kEnumM

theorem cert3372 : (chainCheck .plus = true) ∧ (chainCheck .minus = true)
    ∧ (basicCheck .plus = true) ∧ (basicCheck .minus = true)
    ∧ (∃ T, oSetCheckW .plus T = true ∧ r3CheckW T = true) ∧ (∃ T, oSetCheckW .minus T = true)
    ∧ (∃ S D, s5CheckW .plus S D = true) ∧ (∃ S D, s5CheckW .minus S D = true) :=
  ⟨chainP, chainM, basicP, basicM, ⟨TP, oSetP, r3P⟩, ⟨TM, oSetM⟩, ⟨_, _, s5P⟩, ⟨_, _, s5M⟩⟩

theorem cert3375 : ∃ F, q3CheckW F = true := by
  refine ⟨FP, ?_⟩
  rw [q3CheckW_eq]
  exact q3_sound uArrP_bind ⟨levelsUP.1.2.2.2.1, levelsUP.1.2.2.2.2.1⟩ levelsPP
    ⟨chainOmP.1, chainOmP.2.1, chainOmP.2.2.1⟩ levelsUP flagA_bind flagB_bind bindFP
    (genAP.2 8 (by norm_num)) kG8Can kUPRange (fun y hy => psiTT_eq .plus hy) kLettersQ3
    sigTarget_bind kSigRange kQ3

end CertificateChecks.KernelO8

end
