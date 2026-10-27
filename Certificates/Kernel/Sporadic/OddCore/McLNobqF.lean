module

public import Certificates.Kernel.Sporadic.OddCore.McLNobq
public import Certificates.Kernel.Sporadic.McLK.Final
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.ClassicalInvolution.SmallCases.NobqMcLInputs
public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLNobq

open CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.Nobq
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.VO3
open CertificateChecks.KernelSpor.McLK

theorem base : szOK 275 9 = true ∧ cK (pidn 275 9) = true ∧
    CFSG.KS.Prim.idK 275 9 (mask 9) = true ∧ cK McLNA = true ∧ cK McLNB = true ∧
    allN 275 (fun x => bAnd(Nat.beq (pg 9 (mask 9) McLNA x) (r32 AL x),
      Nat.beq (pg 9 (mask 9) McLNB x) (r32 BE x))) = true ∧
    allN 4 (fun j => bAnd(cK (McLNS.GI j), bAnd(Nat.beq (McLNS.GI j) (sP j),
      Nat.beq (McLNS.G j) (pidn 275 9)))) = true ∧
    penumHdK (pidn 275 9) McLNS.cnt 50000 McLNS.T McLNS.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 275 9 (mask 9) (275 * 9) (pidn 275 9) = true := base.2.1

theorem hid : idT 275 = tabT (unpack 275 9 (pidn 275 9)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem pts {x : Nat} (hx : x < 275) :
    pg 9 (mask 9) McLNA x = r32 AL x ∧ pg 9 (mask 9) McLNB x = r32 BE x := by
  have h := allN_spec base.2.2.2.2.2.1 x hx
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem ta_eq : Ta = tabT (unpack 275 9 McLNA) := by
  unfold Ta
  rw [orb_eq.1]
  simp only [OJ, v3Rec, tabT, unpack]
  apply Array.ext (by simp)
  intro i h1 _
  simp only [Array.getElem_ofFn, Array.getElem_map]
  rw [(pts (by simpa using h1)).1]

theorem tb_eq : Tb = tabT (unpack 275 9 McLNB) := by
  unfold Tb
  rw [orb_eq.1]
  simp only [OJ, v3Rec, tabT, unpack]
  apply Array.ext (by simp)
  intro i h1 _
  simp only [Array.getElem_ofFn, Array.getElem_map]
  rw [(pts (by simpa using h1)).2]

theorem ab_get {l : Nat} (hl : l = 1 ∨ l = 2) :
    abT.getD (l - 1) (idT 275) = tabT (unpack 275 9 (abS l)) ∧
      canonK 275 9 (mask 9) (275 * 9) (abS l) = true := by
  rcases hl with rfl | rfl
  · exact ⟨by rw [abT, ta_eq]; rfl, base.2.2.2.1⟩
  · exact ⟨by rw [abT, tb_eq]; rfl, base.2.2.2.2.1⟩

theorem mem_letters {ws : List (List Nat)} (h : (ws.all fun w => w.all fun l => l == 1 || l == 2) = true)
    {w : List Nat} (hw : w ∈ ws) {l : Nat} (hl : l ∈ w) : l = 1 ∨ l = 2 := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h w hw) l hl
  simpa using this

theorem k_get {j : Nat} (hj : j < 2) :
    kgens.getD j (idT 275) = tabT (unpack 275 9 (kP j)) ∧
      canonK 275 9 (mask 9) (275 * 9) (kP j) = true := by
  have hw : kWords.getD j [] ∈ kWords := by
    rw [List.getD_eq_getElem _ _ (by rw [letters_ok.2.2.1]; exact hj)]
    exact List.getElem_mem _
  have h := wordTbl_unpack (gs := abT) (S := abS) hid hidc (wd := kWords.getD j [])
    fun l hl => ab_get (mem_letters letters_ok.1 hw hl)
  refine ⟨?_, h.2⟩
  unfold kgens kP
  rw [List.getD_eq_getElem _ _ (by simp [letters_ok.2.2.1]; omega), List.getElem_map, ← h.1,
    List.getD_eq_getElem _ _ (by rw [letters_ok.2.2.1]; exact hj)]

theorem ks_get {l : Nat} (hl : l = 1 ∨ l = 2) :
    kgens.getD (l - 1) (idT 275) = tabT (unpack 275 9 (kS l)) ∧
      canonK 275 9 (mask 9) (275 * 9) (kS l) = true :=
  k_get (by omega)

theorem s_get {j : Nat} (hj : j < 4) :
    sgens.getD j (idT 275) = tabT (unpack 275 9 (sP j)) := by
  have hw : sWords.getD j [] ∈ sWords := by
    rw [List.getD_eq_getElem _ _ (by rw [letters_ok.2.2.2]; exact hj)]
    exact List.getElem_mem _
  have h := wordTbl_unpack (gs := kgens) (S := kS) hid hidc (wd := sWords.getD j [])
    fun l hl => ks_get (mem_letters letters_ok.2.1 hw hl)
  unfold sgens sP
  rw [List.getD_eq_getElem _ _ (by simp [letters_ok.2.2.2]; omega), List.getElem_map, ← h.1,
    List.getD_eq_getElem _ _ (by rw [letters_ok.2.2.2]; exact hj)]

theorem gen {j : Nat} (hj : j < 4) : cK (McLNS.GI j) = true ∧ McLNS.GI j = sP j ∧
    McLNS.G j = pidn 275 9 := by
  have h := allN_spec base.2.2.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem s_tabs : TabsOK 275 9 4 McLNS.GI sgens.toArray := by
  have hl : sgens.length = 4 := by simp [sgens, letters_ok.2.2.2]
  refine ⟨by simp [hl], fun j hj => ⟨?_, (gen hj).1⟩⟩
  rw [getElem!_pos _ j (by simpa [hl] using hj), List.getElem_toArray, (gen hj).2.1,
    ← s_get hj, List.getD_eq_getElem]

theorem s_pe : ∀ i < McLNS.cnt, penumPtK 275 9 (mask 9) (275 * 9) true McLNS.G McLNS.GI 4
    McLNS.cnt McLNS.T McLNS.PL McLNS.POS McLNS.SRT McLNS.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < McLNS.cnt,
    hsortPtK 275 9 (mask 9) McLNS.cnt McLNS.T McLNS.HS McLNS.HSI i = true :=
  fun i hi => slK_spec sH i (Nat.zero_le _) (by omega) hi

theorem facts9307 : noncentralInvOK = true := by
  unfold noncentralInvOK
  have hcap : CFSG.ClassicalInvolution.McLProof.capK = 50000 := rfl
  rw [hcap, (mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2.2.2.2 s_pe s_hs).1]
  obtain ⟨i, hi, hn⟩ := List.any_eq_true.1 nc_ok
  have hi' := List.mem_range.1 hi
  have hc : canonK 275 9 (mask 9) (275 * 9) (McLNS.T i) = true := penumPt_canon (s_pe i hi')
  rw [Array.any_eq_true]
  refine ⟨i, by simpa [hRec] using hi', ?_⟩
  simp only [hRec, Array.getElem_ofFn]
  rw [involOK_unpack' (by norm_num) hid hidc hc, ta_eq, tblEq_unpack hc base.2.2.2.1]
  unfold ncAt at hn
  simp only [bAnd_iff] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  rw [h1, h2]
  revert h3
  cases Nat.beq (McLNS.T i) McLNA <;> decide

end CertificateChecks.KernelSpor.McLNobq

end
