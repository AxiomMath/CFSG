module

public import Certificates.Kernel.G24Cls.Chk26991
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PinCheck
public import Certificates.Kernel.Co1B.Tri2045Base
public import Certificates.Kernel.G24Tri.Chk27206

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24.E8x26991

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.ArrEnum CertificateChecks.KernelG24.Tri27206
open CFSG.EvenSporadicStandard.Induction CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
open CFSG.KS.Raw
open CFSG.KC.BfsPin (PP eqA_PP compA_PP invCand_PP idA_eq)

theorem hw : szOK 1365 11 = true := by decide

theorem e8_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem k_parts : permB 1365 11 (LC.S 0) = true ∧ permB 1365 11 (LC.S 1) = true ∧
    e8Facts (e8W co1WordE1) (e8W co1WordE2) (e8W co1WordE3) = true := by
  have h := k26991
  simp only [e8_strictB, bAnd_iff] at h
  exact h

theorem permB_S {h : Nat} (hh : h < 2) : permB 1365 11 (e8S h) = true := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · exact k_parts.1
  · exact k_parts.2.1

theorem permB_SI {h : Nat} (hh : h < 2) : permB 1365 11 (e8SI h) = true :=
  permB_pinvS hw (permB_S hh)

theorem strong_get {h : Nat} (hh : h < 2) : twoBStrong[h]! = unpack 1365 11 (e8S h) := by
  rw [CertificateChecks.KernelCo1B.Tri2045.strong_facts.2 h (by omega),
    Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec kSR h (by omega))]
  rfl

theorem gen_get {h : Nat} (hh : h < 2) : co1GenArr[h]! = unpack 1365 11 (e8S h) := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · exact strong_get (h := 0) (by norm_num)
  · exact strong_get (h := 1) (by norm_num)

theorem inv_get {h : Nat} (hh : h < 2) : co1GenInv[h]! = unpack 1365 11 (e8SI h) := by
  have e : co1GenInv[h]! = invCand 1365 twoBStrong[h]! := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> rfl
  rw [e, strong_get hh]
  exact invCand_PP (pp_of_permB hw (permB_S hh))

theorem isInv_get {h : Nat} (hh : h < 2) :
    isInvA 1365 twoBStrong[h]! (invCand 1365 twoBStrong[h]!) = true := by
  have hk : invEqK 1365 11 (mask 11) (1365 * 11) (e8S h) (e8SI h) = true := permB_S hh
  rw [strong_get hh, (CFSG.KS.Prim.invEqK_sound hk).1]
  exact (CFSG.KS.Prim.invEqK_sound hk).2

theorem word_eq {wd : List Int} (hl : lettersOK 2 wd = true) :
    co1ArrWord wd = unpack 1365 11 (e8W wd) ∧ PP 1365 11 (e8W wd) :=
  ⟨wordA_unpack hw (fun h hh => gen_get hh) (fun h hh => inv_get hh) (fun h hh => permB_S hh)
    (fun h hh => permB_SI hh) hl,
    pp_of_permB hw (permB_wordK hw (fun h hh => permB_S hh) (fun h hh => permB_SI hh) hl)⟩

theorem l1 : lettersOK 2 co1WordE1 = true := by decide

theorem l2 : lettersOK 2 co1WordE2 = true := by decide

theorem l3 : lettersOK 2 co1WordE3 = true := by decide

theorem m_eq {p q : Nat} (hp : PP 1365 11 p) (hq : PP 1365 11 q) :
    compA 1365 (unpack 1365 11 p) (unpack 1365 11 q) = unpack 1365 11 (e8M p q) :=
  compA_PP hp hq

theorem pm {p q : Nat} (hp : PP 1365 11 p) (hq : PP 1365 11 q) : PP 1365 11 (e8M p q) := hp.mul hq

theorem co1E8Check_true : co1E8Check = true := by
  obtain ⟨wA, pA⟩ := word_eq l1
  obtain ⟨wB, pB⟩ := word_eq l2
  obtain ⟨wC, pC⟩ := word_eq l3
  have pI : PP 1365 11 (pidn 1365 11) := CFSG.KC.BfsPin.PP.id hw
  have hf := k_parts.2.2
  unfold e8Facts at hf
  simp only [bAnd_iff] at hf
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ := hf
  simp only [co1E8Check]
  rw [isInv_get (h := 0) (by norm_num), isInv_get (h := 1) (by norm_num), l1, l2, l3, wA, wB, wC,
    m_eq pA pA, m_eq pB pB, m_eq pC pC, m_eq pA pB, m_eq pB pA, m_eq pA pC, m_eq pC pA,
    m_eq pB pC, m_eq pC pB, idA_eq hw, eqA_PP (pm pA pA) pI, eqA_PP (pm pB pB) pI,
    eqA_PP (pm pC pC) pI, eqA_PP (pm pA pB) (pm pB pA), eqA_PP (pm pA pC) (pm pC pA),
    eqA_PP (pm pB pC) (pm pC pB), eqA_PP pA pI, eqA_PP pB pI, eqA_PP pB pA, eqA_PP pC pI,
    eqA_PP pC pA, eqA_PP pC pB, eqA_PP pC (pm pA pB)]
  simp only [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, Bool.and_self]

end CertificateChecks.KernelG24.E8x26991

end
