module

public import Certificates.Kernel.Sporadic.OddCore.SuzRTC
public import Certificates.Kernel.Sporadic.OddCore.SuzRTC1
public import Certificates.Kernel.Sporadic.OddCore.SuzRKZF
public import Certificates.Kernel.Sporadic.L2.Vtx
public import Certificates.Kernel.Sporadic.L2.G6
public import CFSG.Certificates.Kernel.Spor.CEnumSound

public section

namespace CertificateChecks.KernelSpor.SuzRTF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KS.KeyBfsG CFSG.KS.CEnum
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.RootTwistCheck
open CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck (conjA t1A commA aA bA)
open CFSG.Sporadic.SuzRecog.LevelTwo (fp)
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzRTK
open CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P commA_P)

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Idn" => pidn 1782 11

theorem and_parts {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa [Bool.and_eq_true] using h

theorem hb : baseK = true := kBase

theorem cnX : cn XT = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1

theorem cnXI : cn XTI = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem cnY : cn YT = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem cnYI : cn YTI = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem ieX : ie XT XTI = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

theorem ieY : ie YT YTI = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem msX : msift XT = true ∧ msift YT = true ∧ msift (SuzRKG 0) = true ∧
    msift (SuzRKG 1) = true := by
  have h := hb
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem pX : P xTwArr XT := by
  refine ⟨?_, cnX⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzRTX.all 0 (by norm_num)
  rw [← SuzRTX.eq, Nat.mul_zero] at h
  exact h

theorem pY : P yTwArr YT := by
  refine ⟨?_, cnY⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzRTY.all 0 (by norm_num)
  rw [← SuzRTY.eq, Nat.mul_zero] at h
  exact h

theorem pXI : P (invCand 1782 xTwArr) XTI ∧ isInvA 1782 xTwArr (invCand 1782 xTwArr) = true :=
  SuzMGF.p_invR pX ieX cnXI

theorem pYI : P (invCand 1782 yTwArr) YTI ∧ isInvA 1782 yTwArr (invCand 1782 yTwArr) = true :=
  SuzMGF.p_invR pY ieY cnYI

theorem pRho : P rhoArr RHO := SuzTwCF.pRho

theorem pRhoI : P (invCand 1782 rhoArr) RHOI := L2G.pRhoI

theorem pT1 : P t1A T1P := SuzTwCF.pT1

theorem pW0 : P w0Arr W0 := SuzTwCF.pW0

theorem hvA : ∀ i < 2835, aVt i = true := L2G.hvA L2G.vtxOK

theorem hvW : ∀ j < 162, tVt j = true := L2G.hvW L2G.vtxOK

theorem pAP : P aPrimeArr AP := by
  unfold aPrimeArr
  rw [L2G.p1_eq]
  exact L2G.pA hvA (by norm_num)

theorem pV : P vRootArr VR := L2G.pW hvW (by norm_num)

theorem pV' : P vRoot'Arr VR' := L2G.pW hvW (by norm_num)

theorem pKA : P kGenAArr (SuzRKG 0) := ⟨SuzRKF.kGenA_eq, SuzRKZF.canG (by norm_num)⟩

theorem pKB : P kGenBArr (SuzRKG 1) := ⟨SuzRKF.kGenB_eq, SuzRKZF.canG (by norm_num)⟩

theorem conj_P {g a : Array Nat} {G GI A : Nat} (hg : P g G) (hgi : P (invCand 1782 g) GI)
    (ha : P a A) : P (conjA g a) (pc G (pc A GI)) := p_comp hg (p_comp ha hgi)

theorem pV1 : P vRoot1A V1 := conj_P pRho pRhoI pV

theorem pV1' : P vRoot1A' V1' := conj_P pRho pRhoI pV'

theorem permOK_of {g : Array Nat} {G GI : Nat} (hg : g = unpack 1782 11 G) (h : ie G GI = true) :
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK g = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK
  rw [hg, (invEqK_sound h).1]
  exact (invEqK_sound h).2

theorem powA_P {t : Array Nat} {T : Nat} (ht : P t T) :
    ∀ k, P (powA 1782 t k) (SuzMGF.powK T k)
  | 0 => pidn_P
  | k + 1 => p_comp ht (powA_P ht k)

theorem permsOK_true : permsOK = true := by
  unfold permsOK
  have hA := (L2G.aVt_parts (hvA 342 (by norm_num))).2.2.2
  have hV := (L2G.tVt_parts (hvW 135 (by norm_num))).2.2.2.2.2.1
  have hV' := (L2G.tVt_parts (hvW 55 (by norm_num))).2.2.2.2.2.1
  rw [permOK_of pRho.1 (allN_spec SuzTwCF.gInv 2 (by norm_num)), permOK_of pAP.1 hA,
    permOK_of pV.1 hV, permOK_of pV'.1 hV', permOK_of pX.1 ieX, permOK_of pY.1 ieY]
  rfl

theorem membersOK_true : membersOK = true := by
  have hm := SuzMGF.kMem
  simp only [Bool.and_eq_true] at hm
  unfold membersOK
  rw [inM_eq pRho.1 pRho.2, inM_eq pX.1 pX.2, inM_eq pY.1 pY.2, msX.1, msX.2.1]
  simp only [Bool.and_true]
  exact hm.1.1.1.1.1.1

theorem commOK_true : CFSG.Sporadic.SuzRecog.RootTwistCheck.commOK = true := by
  unfold CFSG.Sporadic.SuzRecog.RootTwistCheck.commOK
  rw [commA_P pRho pT1, commA_P pRho pAP, commA_P pX pT1, commA_P pX pAP, commA_P pY pT1,
    commA_P pY pAP]
  exact kComm

theorem inV_P {v v₁ z : Array Nat} {V V₁ Z : Nat} (hv : P v V) (hv₁ : P v₁ V₁) (hz : P z Z) :
    inV v v₁ z = inVK V V₁ Z := by
  unfold inV inVK
  rw [eqA_P hz hv, eqA_P hz hv₁, eqA_P hz (p_comp hv hv₁)]

theorem normV_P {v v₁ g : Array Nat} {V V₁ G GI : Nat} (hv : P v V) (hv₁ : P v₁ V₁) (hg : P g G)
    (hgi : P (invCand 1782 g) GI) : normV v v₁ g = normVK V V₁ G GI := by
  unfold normV normVK
  rw [inV_P hv hv₁ (conj_P hg hgi hv), inV_P hv hv₁ (conj_P hg hgi hv₁)]

theorem normOK_true : normOK = true := by
  unfold normOK
  rw [normV_P pV pV1 pRho pRhoI, normV_P pV pV1 pX pXI.1, normV_P pV' pV1' pRho pRhoI,
    normV_P pV' pV1' pY pYI.1]
  exact kNorm

theorem sqOK_true : sqOK = true := by
  have h := kSq
  unfold sqK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hR2 := powA_P pRho 2
  have hR2I : P (invCand 1782 (powA 1782 rhoArr 2)) (SuzMGF.powK RHOI 2) := by
    refine ⟨?_, (powA_P pRhoI 2).2⟩
    rw [hR2.1]
    exact (invEqK_sound h4).1
  unfold sqOK
  rw [eqA_P (powA_P pRho 3) pidn_P, eqA_P (powA_P (p_comp pX pY) 2) pidn_P,
    eqA_P (powA_P (p_comp pX (conj_P pRho pRhoI pY)) 2) pidn_P,
    eqA_P (powA_P (p_comp pX (conj_P hR2 hR2I pY)) 2) pidn_P, h1, h2, h3, h5]
  rfl

theorem evenOK_true : evenOK = true := by
  unfold evenOK
  rw [commA_P (p_comp pX pRhoI) pV, commA_P (p_comp pX pRhoI) pV1, commA_P (p_comp pY pRho) pV',
    commA_P (p_comp pY pRho) pV1']
  exact kEven

theorem kGenOK_true : kGenOK = true := by
  have h := kKGen
  unfold kGenK cmK at h
  unfold kGenOK
  rw [permOK_of pKA.1 SuzRKC.iA, permOK_of pKB.1 SuzRKC.iB, inM_eq pKA.1 pKA.2,
    inM_eq pKB.1 pKB.2, msX.2.2.1, msX.2.2.2, commA_P pKA pT1, commA_P pKB pT1,
    commA_P pKA pRho, commA_P pKB pRho]
  simpa using h

theorem classSearch_eq : rhoClassSearch = keyBfsG (fun g => fp (conjA g rhoArr))
    (fun s x => compA 1782 cGens[s]! x) 2 (idA 1782) (fp rhoArr) 960 :=
  rhoClassSearch_def.trans rfl

theorem cGens_eq {s : Nat} (hs : s < 2) : cGens[s]! = unpack 1782 11 (SuzMGG s) := by
  interval_cases s
  · simp only [cGens, List.getElem!_toArray, List.getElem!_cons_zero]
    exact SuzMGF.pAa.1
  · simp only [cGens, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact SuzMGF.pBb.1

theorem cpt_of {lo len i : Nat}
    (h : cenumSlK 1782 11 (mask 11) (1782 * 11) 2 960 RHO SuzMGG SuzMGGI SuzRCT SuzRCTI SuzRCPL
      SuzRCPOS SuzRCFP SuzRCSRT SuzRCSRI lo len = true) (h1 : lo ≤ i) (h2 : i < lo + len)
    (h3 : i < 960) :
    cenumPtK 1782 11 (mask 11) (1782 * 11) 2 960 RHO SuzMGG SuzMGGI SuzRCT SuzRCTI SuzRCPL SuzRCPOS
      SuzRCFP SuzRCSRT SuzRCSRI i = true := by
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i 960 = true := by simpa [Nat.blt_eq] using h3
  rw [hb] at h'
  exact h'

theorem cSlices : ∀ i < 960, cenumPtK 1782 11 (mask 11) (1782 * 11) 2 960 RHO SuzMGG SuzMGGI
    SuzRCT SuzRCTI SuzRCPL SuzRCPOS SuzRCFP SuzRCSRT SuzRCSRI i = true := by
  intro i hi
  have hs : ∀ s < 12, cSl s = true := by
    intro s hs
    interval_cases s
    exacts [cSl0, cSl1, cSl2, cSl3, cSl4, cSl5, cSl6, cSl7, cSl8, cSl9, cSl10, cSl11]
  have h := hs (i / 80) (by omega)
  unfold cSl at h
  exact cpt_of h (by change 80 * (i / 80) ≤ i; omega) (by change i < 80 * (i / 80) + 80; omega) hi

theorem crec :
    keyBfsG (fun g => fp (conjA g rhoArr)) (fun s x => compA 1782 cGens[s]! x) 2 (idA 1782)
        (fp rhoArr) 960 =
        (Array.ofFn (n := 960) fun i => unpack 1782 11 (SuzRCT i.val),
          Array.ofFn (n := 960) fun i => if i.val = 0 then 0 else SuzRCPL i.val / 2,
          Array.ofFn (n := 960) fun i => if i.val = 0 then 0 else SuzRCPL i.val % 2) ∧
      (∀ i < 960, invCand 1782 (unpack 1782 11 (SuzRCT i)) = unpack 1782 11 (SuzRCTI i) ∧
        isInvA 1782 (unpack 1782 11 (SuzRCT i)) (unpack 1782 11 (SuzRCTI i)) = true) ∧
      (∀ a < 960, ∀ b < 960, fp (conjA (unpack 1782 11 (SuzRCT a)) rhoArr) =
        fp (conjA (unpack 1782 11 (SuzRCT b)) rhoArr) → a = b) ∧
      (∀ i < 960, 0 < i → SuzRCPL i / 2 < i ∧ SuzRCPL i % 2 < 2 ∧
        compA 1782 cGens[SuzRCPL i % 2]! (unpack 1782 11 (SuzRCT (SuzRCPL i / 2))) =
          unpack 1782 11 (SuzRCT i)) ∧
      (∀ i < 960, cn (SuzRCT i) = true) :=
  cenumK_sound (k := 2) (cnt := 960) (cap := 960) (gens := cGens) (root := idA 1782)
    (rho := rhoArr) (fun _ hs => cGens_eq hs) SuzRKF.idA_eq pRho.1 kCHd cSlices le_rfl

theorem cTr_eq : cTr = Array.ofFn (n := 960) fun i => unpack 1782 11 (SuzRCT i.val) := by
  unfold cTr
  rw [classSearch_eq, crec.1]

theorem cTr_get {i : Nat} (hi : i < 960) : cTr[i]! = unpack 1782 11 (SuzRCT i) := by
  rw [cTr_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem cPar_get {i : Nat} (hi : i < 960) (h0 : 0 < i) : cPar[i]! = SuzRCPL i / 2 := by
  unfold cPar
  rw [classSearch_eq, crec.1, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp [Nat.pos_iff_ne_zero.1 h0]

theorem cLab_get {i : Nat} (hi : i < 960) (h0 : 0 < i) : cLab[i]! = SuzRCPL i % 2 := by
  unfold cLab
  rw [classSearch_eq, crec.1, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp [Nat.pos_iff_ne_zero.1 h0]

theorem cTr_size : cTr.size = 960 := by
  rw [cTr_eq, Array.size_ofFn]

theorem cTab_get {j : Nat} (hj : j < 960) :
    cTab.getD (CFSG.Sporadic.SuzRecog.LevelTwo.fp (conjA cTr[j]! rhoArr)) 960 = j := by
  have e : cTab = keyTab (fun g => CFSG.Sporadic.SuzRecog.LevelTwo.fp (conjA g rhoArr)) cTr := rfl
  rw [e]
  refine keyTab_getD (κ := fun g => CFSG.Sporadic.SuzRecog.LevelTwo.fp (conjA g rhoArr))
    (fun a ha b hb h => ?_) (by rw [cTr_size]; exact hj) 960
  rw [cTr_size] at ha hb
  rw [cTr_get ha, cTr_get hb] at h
  exact crec.2.2.1 a ha b hb h

theorem classOK_true : classOK = true := by
  have hm := SuzMGF.kMem
  simp only [Bool.and_eq_true] at hm
  have hc := SuzMGF.kComm
  simp only [Bool.and_eq_true] at hc
  have hT0 : SuzRCT 0 = Idn := by
    have h := kCHd
    unfold cHdK cenumHdK at h
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.2.2.1
  unfold classOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨permOK_of SuzMGF.pAa.1 (SuzMGF.inv.1 0 (by norm_num)),
    permOK_of SuzMGF.pBb.1 (SuzMGF.inv.1 1 (by norm_num))⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, cTr_size⟩, ?_⟩, ?_⟩
  · rw [inM_eq SuzMGF.pAa.1 SuzMGF.pAa.2]
    exact hm.1.1.1.2
  · rw [inM_eq SuzMGF.pBb.1 SuzMGF.pBb.2]
    exact hm.1.1.2
  · rw [commA_P SuzMGF.pAa pT1]
    exact hc.1.1.1.2
  · rw [commA_P SuzMGF.pBb pT1]
    exact hc.1.1.2
  · rw [cTr_get (by norm_num), hT0, ← SuzRKF.idA_eq]
    exact SuzRKF.eqA_self _
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨?_, cTab_get hi⟩, ?_⟩
  · unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK
    rw [cTr_get hi, (crec.2.1 i hi).1]
    exact (crec.2.1 i hi).2
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · right
      obtain ⟨t1, t2, t3⟩ := crec.2.2.2.1 i hi h0
      rw [cPar_get hi h0, cLab_get hi h0]
      refine ⟨⟨t1, t2⟩, ?_⟩
      rw [cTr_get hi, cTr_get (by omega), t3]
      exact SuzRKF.eqA_self _

end CertificateChecks.KernelSpor.SuzRTF

end
