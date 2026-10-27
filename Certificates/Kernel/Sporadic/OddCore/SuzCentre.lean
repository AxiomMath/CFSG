module

public import Certificates.Kernel.Sporadic.OddCore.SuzFusion
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.Certificates.Kernel.SuzCentreKSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSpor.SuzCentre

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.KC.SuzCentreK CFSG.ComponentClassification.AS81.SuzCenter
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

@[expose] noncomputable def LT (j : Nat) : Nat := nIf(Nat.blt j 11, SuzFusT.F j, SuzFusI 0)

@[expose] noncomputable def RG (k : Nat) : Nat := wordK LT (sylMWords.getD k [])

theorem kS : centreK 11 SuzFusT.F sylSZWord sylSLevels 16384 = true := by quickRfl

theorem kR : centreK 22 RG sylRZWord sylRLevels 8192 = true := by quickRfl

theorem kU : permOK 1782 11 (mask 11) (1782 * 11) (SuzFusI 0) (SuzFusT.F 0) = true := by quickRfl

theorem kM : allN 22 (fun k => msift (RG k)) = true := by quickRfl

theorem kSz : szOK 1782 11 = true := by quickRfl

theorem kWords : (sylMWords.length == 22 && sylMWords.all (·.all (· < 12))) = true := by
  decide +kernel

theorem suzSylowCenterCheck_true : suzSylowCenterCheck = true := by
  have pF : ∀ k < 53, PP 1782 11 (SuzFusT.F k) := fun k hk =>
    @PP_of_permOK' 1782 11 (SuzFusT.F k) (SuzFusI k) kSz (allN_spec fus_perms k hk)
  have pU : PP 1782 11 (SuzFusI 0) := PP_of_permOK' kSz kU
  have pLT : ∀ j < 12, PP 1782 11 (LT j) := by
    intro j hj
    unfold LT
    by_cases h : j < 11
    · rw [Nat.blt_eq.mpr h]
      exact pF j (by omega)
    · have hf : Nat.blt j 11 = false := by
        cases e : Nat.blt j 11
        · rfl
        · exact absurd (Nat.blt_eq.mp e) h
      rw [hf]
      exact pU
  have eS : invSylowArrs = Array.ofFn (n := 11) fun k => unpack 1782 11 (SuzFusT.F k.val) := by
    rw [show invSylowArrs = Array.ofFn (n := 11) fun j => invFusionRun j.val from rfl]
    apply Array.ext (by simp)
    intro i h1 h2
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    exact fusionRun_eq (by simp at h1; omega)
  have eU : invCand 1782 invSylowArrs[0]! = unpack 1782 11 (SuzFusI 0) := by
    rw [eS, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
    exact (invEqK_sound (allN_spec fus_perms 0 (by omega))).1
  have hS : invSylowArrs.size = 11 := by rw [eS]; simp
  have eL : sylLetters = Array.ofFn (n := 12) fun j => unpack 1782 11 (LT j.val) := by
    apply Array.ext (by simp [sylLetters, hS])
    intro i h1 h2
    rw [Array.getElem_ofFn]
    have hi : i < 12 := by simpa using h2
    by_cases h : i < 11
    · simp only [sylLetters]
      rw [Array.getElem_push_lt (by rw [hS]; exact h),
        ← getElem!_pos invSylowArrs i (by rw [hS]; exact h), eS,
        getElem!_pos _ i (by simp; exact h), Array.getElem_ofFn]
      unfold LT
      rw [Nat.blt_eq.mpr h]
    · have hi11 : i = 11 := by omega
      subst hi11
      simp only [sylLetters, Array.getElem_push, hS, Nat.lt_irrefl, ↓reduceDIte]
      rw [eU]
      rfl
  have hwl := kWords
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hwl
  obtain ⟨hlen, hlt⟩ := hwl
  have wR : ∀ k < 22, wordC sylLetters (sylMWords.getD k []) = unpack 1782 11 (RG k) ∧
      PP 1782 11 (RG k) := by
    intro k hk
    rw [eL]
    exact wordC_unpack kSz pLT _ fun j hj => hlt _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _) j hj
  have eR : sylMGens = Array.ofFn (n := 22) fun k => unpack 1782 11 (RG k.val) := by
    apply Array.ext (by simp [sylMGens, hlen])
    intro k h1 h2
    have hk : k < 22 := by simpa using h2
    rw [Array.getElem_ofFn, ← (wR k hk).1, List.getD_eq_getElem _ _ (by omega)]
    simp [sylMGens]
  unfold suzSylowCenterCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨centreK_sound eS (fun k hk => pF k (by omega)) kS, ?_⟩,
    centreK_sound eR (fun k hk => (wR k hk).2) kR⟩
  unfold allBelow
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hk' : k < 22 := by rw [eR] at hk; simpa using hk
  have e : sylMGens[k]! = unpack 1782 11 (RG k) := by
    rw [getElem!_pos _ k hk]
    simp [eR]
  have hp := (wR k hk').2
  rw [e, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold CFSG.Sporadic.SuzOddCore.permOK
    rw [Bool.and_eq_true, beq_iff_eq]
    exact ⟨by simp [unpack], validA_unpack (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2)⟩
  · rw [inM_eq rfl hp.1]
    exact allN_spec kM k hk'

end CertificateChecks.KernelSpor.SuzCentre

end
