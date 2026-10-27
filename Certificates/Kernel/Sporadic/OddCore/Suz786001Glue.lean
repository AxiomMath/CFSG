module

public import CFSG.Sporadic.SuzOddCore.Perms
public import Certificates.Kernel.Sporadic.OddCore.Suz786001Fus
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CertificateChecks.KernelSpor.Suz786001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.ComponentClassification.GrSLit.L34Sec5S CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.GSThmB.CF23L34
open CFSG.KC.BfsPin (PP compA_PP invCand_PP)

theorem pp0 : PP 1782 11 (Suz786001T.F 0) := pp_of_permB kSz kPermY1

theorem pp1 : PP 1782 11 (Suz786001T.F 1) := pp_of_permB kSz kPermY2

theorem pp2 : PP 1782 11 (Suz786001T.F 2) := pp_of_permB kSz kPermM

theorem gens_size : suzCtrlGens.size = 4 := by simp [suzCtrlGens]

theorem gens_eq {h : Nat} (hh : h < 4) :
    suzCtrlGens[h]! = unpack 1782 11 (SC h) ∧ PP 1782 11 (SC h) := by
  have hh' : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by omega
  rcases hh' with rfl | rfl | rfl | rfl
  · exact ⟨y1_eq, pp0⟩
  · exact ⟨y2_eq, pp1⟩
  · have e : suzCtrlGens[2]! =
        compA 1782 (compA 1782 suzMArr suzY1Arr) (invCand 1782 suzMArr) := by
      simp [suzCtrlGens]
    refine ⟨?_, (pp2.mul pp0).mul pp2.inv⟩
    rw [e, y1_eq, m_eq, invCand_PP pp2, compA_PP pp2 pp0, compA_PP (pp2.mul pp0) pp2.inv]
    rfl
  · have e : suzCtrlGens[3]! =
        compA 1782 (compA 1782 suzMArr suzY2Arr) (invCand 1782 suzMArr) := by
      simp [suzCtrlGens]
    refine ⟨?_, (pp2.mul pp1).mul pp2.inv⟩
    rw [e, y2_eq, m_eq, invCand_PP pp2, compA_PP pp2 pp1, compA_PP (pp2.mul pp1) pp2.inv]
    rfl

theorem gensInv_eq {h : Nat} (hh : h < 4) :
    suzCtrlGensInv[h]! = unpack 1782 11 (SIC h) := by
  rw [suzCtrlGensInv, getElem!_pos _ h (by simpa [gens_size] using hh), Array.getElem_map,
    ← getElem!_pos suzCtrlGens h (by rw [gens_size]; exact hh), (gens_eq hh).1,
    invCand_PP (gens_eq hh).2]
  rfl

theorem wordA_b {wd : List Int} {B : Nat} (hl : lettersOK 4 wd = true)
    (hw : Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SC SIC wd) B = true) :
    wordA 1782 suzCtrlGens suzCtrlGensInv wd = unpack 1782 11 B := by
  rw [wordA_eq kSz (fun h hh => (gens_eq hh).1) (fun h hh => gensInv_eq hh)
    (fun h hh => permB_of_pp (gens_eq hh).2) (fun h hh => permB_of_pp (gens_eq hh).2.inv) wd hl,
    Nat.eq_of_beq_eq_true hw]

noncomputable def gs (i : ℕ) : Equiv.Perm (Fin 1782) :=
  if i = 0 then permOfArr 1782 suzY1Arr else if i = 1 then permOfArr 1782 suzY2Arr
    else if i = 2 then
      permOfArr 1782 suzMArr * permOfArr 1782 suzY1Arr * (permOfArr 1782 suzMArr)⁻¹
    else permOfArr 1782 suzMArr * permOfArr 1782 suzY2Arr * (permOfArr 1782 suzMArr)⁻¹

theorem isInv_of {t : Array Nat} {P : Nat} (ht : t = unpack 1782 11 P) (hP : PP 1782 11 P) :
    isInvA 1782 t (invCand 1782 t) = true := by
  rw [ht, invCand_PP hP]
  exact CFSG.KS.Raw.Orb.isInvA_unpack (permB_of_pp hP)

theorem rep_gs {h : Nat} (hh : h < 4) : Rep 1782 suzCtrlGens[h]! (gs h) := by
  have r1 := (rep_permOfArr (isInv_of y1_eq pp0)).1
  have r2 := (rep_permOfArr (isInv_of y2_eq pp1)).1
  have rm := rep_permOfArr (isInv_of m_eq pp2)
  have hh' : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by omega
  rcases hh' with rfl | rfl | rfl | rfl
  · exact r1
  · exact r2
  · have e : suzCtrlGens[2]! =
        compA 1782 (compA 1782 suzMArr suzY1Arr) (invCand 1782 suzMArr) := by
      simp [suzCtrlGens]
    rw [e]
    exact rep_compA (rep_compA rm.1 r1) rm.2
  · have e : suzCtrlGens[3]! =
        compA 1782 (compA 1782 suzMArr suzY2Arr) (invCand 1782 suzMArr) := by
      simp [suzCtrlGens]
    rw [e]
    exact rep_compA (rep_compA rm.1 r2) rm.2

theorem rep_gsInv {h : Nat} (hh : h < 4) : Rep 1782 suzCtrlGensInv[h]! (gs h)⁻¹ := by
  refine rep_inv_of_isInvA (rep_gs hh) ?_
  rw [(gens_eq hh).1, gensInv_eq hh]
  exact CFSG.KS.Raw.Orb.isInvA_unpack (permB_of_pp (gens_eq hh).2)

theorem le_closure :
    suzM ≤ Subgroup.closure {permOfArr 1782 suzY1Arr, permOfArr 1782 suzY2Arr,
      permOfArr 1782 suzMArr * permOfArr 1782 suzY1Arr * (permOfArr 1782 suzMArr)⁻¹,
      permOfArr 1782 suzMArr * permOfArr 1782 suzY2Arr * (permOfArr 1782 suzMArr)⁻¹} := by
  have hsub : Set.range (fun h : Fin 4 => gs h) ⊆ {permOfArr 1782 suzY1Arr,
      permOfArr 1782 suzY2Arr,
      permOfArr 1782 suzMArr * permOfArr 1782 suzY1Arr * (permOfArr 1782 suzMArr)⁻¹,
      permOfArr 1782 suzMArr * permOfArr 1782 suzY2Arr * (permOfArr 1782 suzMArr)⁻¹} := by
    rintro _ ⟨h, rfl⟩
    fin_cases h <;> simp [gs]
  have hw : ∀ {wd : List Int} {B : Nat} {b : Equiv.Perm (Fin 1782)},
      lettersOK 4 wd = true →
      Nat.beq (wordK 1782 11 (mask 11) (pidn 1782 11) SC SIC wd) B = true →
      Rep 1782 (unpack 1782 11 B) b →
      b ∈ Subgroup.closure (Set.range (fun h : Fin 4 => gs h)) := by
    intro wd B b hl hk hb
    have r := rep_wordA (fun h hh => rep_gs hh) (fun h hh => rep_gsInv hh) wd hl
    rw [wordA_b hl hk] at r
    rw [← r.unique hb]
    exact Quiver.SchreierGraph.evalWord_mem_closure _ _
  rw [suzM, Subgroup.closure_le]
  intro g hg
  refine Subgroup.closure_mono hsub ?_
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · refine hw kLetters0 kWord0 ?_
    rw [← Suz2306.b0Arr_eq]
    exact rep_b0
  · refine hw kLetters1 kWord1 ?_
    rw [← Suz2306.b1Arr_eq]
    exact rep_b1

end CertificateChecks.KernelSpor.Suz786001

end
