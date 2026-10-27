module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZfGens
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QT2ASyl
public import CFSG.Sporadic.J4.QT2LocVLBasic
public import CFSG.Sporadic.J4.QT2LocZCentMain
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.Kernel.J4Q.ZFr

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem zfSeqW_cons (g : ℕ) (s : List ℕ) : zfSeqW (g :: s) = zcGenWords.getD g [] ++ zfSeqW s := by
  simp [zfSeqW]

theorem el5_nil : el5 [] = 1 := by simp [el5, wordProd]

theorem zfSeqW_letters : ∀ s : List ℕ, (∀ g ∈ s, g < 3) → ∀ l ∈ zfSeqW s, l ∈ letters
  | [], _ => by simp [zfSeqW]
  | g :: s, hs => by
    rw [zfSeqW_cons]
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact zcGenWords_letters _ (zcGenWords_mem (hs g List.mem_cons_self)) l hl
    · exact zfSeqW_letters s (fun x hx => hs x (List.mem_cons_of_mem _ hx)) l hl

theorem letters_ne_zero : ∀ l ∈ letters, l ≠ 0 := by decide

theorem acts_zfSeq (hM : MatFacts) :
    ∀ s : List ℕ, (∀ g ∈ s, g < 3) → Acts (el5 (zfSeqW s)) (zfSeqT s)
  | [], _ => by
    rw [show zfSeqW [] = [] from rfl, el5_nil]
    exact Acts.one
  | g :: s, hs => by
    rw [zfSeqW_cons, QT2.el5_append]
    exact (zcGen_acts hM (hs g List.mem_cons_self)).mul
      (acts_zfSeq hM s fun x hx => hs x (List.mem_cons_of_mem _ hx))

theorem fix_zfSeq (hG : ZfGens) : ∀ s : List ℕ, (∀ g ∈ s, g < 3) → actT (zfSeqT s) 1 = 1
  | [], _ => actT_idT (by norm_num)
  | g :: s, hs => by
    change actT (compT (zcGenTabs.getD g []) (zfSeqT s)) 1 = 1
    rw [actT_comp, fix_zfSeq hG s fun x hx => hs x (List.mem_cons_of_mem _ hx)]
    exact (hG.2 g (hs g List.mem_cons_self)).2

theorem Mx_zfSeq (hM : MatFacts) : ∀ s : List ℕ, Mx (el5 (zfSeqW s)) = rowsMatrix (zfSeqR s)
  | [] => by
    rw [show zfSeqW [] = [] from rfl, el5_nil, map_one]
    exact rowsMatrix_idRows.symm
  | g :: s => by
    rw [zfSeqW_cons, QT2.el5_append, map_mul, Mx_el5 hM, Mx_zfSeq hM s]
    exact (rowsMatrix_mulRows _ _).symm

theorem el5_inv {w : List ℤ} (hw : ∀ l ∈ w, l ∈ letters) : (el5 w)⁻¹ = el5 (invW w) := by
  rw [invW_eq]
  unfold el5
  exact (wordProd_invWord gen5 _ fun l hl => letters_ne_zero l (hw l hl)).symm

theorem Mx_zfSeq_inv_mul (hM : MatFacts) : ∀ (s : List ℕ), (∀ g ∈ s, g < 3) → ∀ (a : J) (A : Array V2),
    Mx a = rowsMatrix A →
    Mx ((el5 (zfSeqW s))⁻¹ * a) =
      rowsMatrix (s.foldl (fun acc g => mulRows (wR (invW (zcGenWords.getD g []))) acc) A)
  | [], _, a, A, h => by
    rw [show zfSeqW [] = [] from rfl, el5_nil, inv_one, one_mul]
    exact h
  | g :: s, hs, a, A, h => by
    have hg := hs g List.mem_cons_self
    have hl := zcGenWords_letters _ (zcGenWords_mem hg)
    rw [zfSeqW_cons, QT2.el5_append, mul_inv_rev, mul_assoc, List.foldl_cons]
    refine Mx_zfSeq_inv_mul hM s (fun x hx => hs x (List.mem_cons_of_mem _ hx)) _ _ ?_
    rw [el5_inv hl, map_mul, Mx_el5 hM, h]
    exact (rowsMatrix_mulRows _ _).symm

theorem Mx_zfSeq_inv (hM : MatFacts) (s : List ℕ) (hs : ∀ g ∈ s, g < 3) :
    Mx (el5 (zfSeqW s))⁻¹ = rowsMatrix (zfSeqRi s) := by
  have h := Mx_zfSeq_inv_mul hM s hs 1 idRows (by rw [map_one]; exact rowsMatrix_idRows.symm)
  rw [mul_one] at h
  exact h

theorem actT_inj_of_acts (hM : MatFacts) {g : J} {T : List ℕ} (h : Acts g T) {c d : ℕ} (hc : c < 2048)
    (hd : d < 2048) (e : actT T c = actT T d) : c = d := by
  have e1 : g * eta uJ 11 c * g⁻¹ = g * eta uJ 11 d * g⁻¹ := by
    rw [h.2 c hc, h.2 d hd, e]
  exact eta_inj hM c hc d hd (mul_left_cancel (mul_right_cancel e1))


theorem wfRows_letter' (hG : ZfGens) (l : ℤ) (hl : l ∈ letters) :
    wfRows (if 0 < l then (g5Mats ())[l.toNat - 1]?.getD idRows
      else (g5Invs ())[(-l).toNat - 1]?.getD idRows) = true := by
  have h := hG.1
  unfold zcLocWf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hs1, hs2⟩, hw1⟩, hw2⟩ := h
  simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [g5Mats] using wf_getD_append (B := baseMats) hs1 hw1 (k := 0) (by norm_num)
  · simpa [g5Mats] using wf_getD_append (B := baseMats) hs1 hw1 (k := 1) (by norm_num)
  · simpa [g5Mats] using wf_getD_append (B := baseMats) hs1 hw1 (k := 2) (by norm_num)
  · simpa [g5Invs] using wf_getD_append (B := baseInvs) hs2 hw2 (k := 0) (by norm_num)
  · simpa [g5Invs] using wf_getD_append (B := baseInvs) hs2 hw2 (k := 1) (by norm_num)
  · simpa [g5Invs] using wf_getD_append (B := baseInvs) hs2 hw2 (k := 2) (by norm_num)

theorem wfRows_foldl_letters' (hG : ZfGens) (w : List ℤ) (hw : ∀ l ∈ w, l ∈ letters)
    (acc : Array V2) (hacc : wfRows acc = true) :
    wfRows (w.foldl (fun a l => mulRows a (if 0 < l then (g5Mats ())[l.toNat - 1]?.getD idRows
      else (g5Invs ())[(-l).toNat - 1]?.getD idRows)) acc) = true := by
  induction w generalizing acc with
  | nil => simpa using hacc
  | cons l w ih =>
    simp only [List.foldl_cons]
    exact ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
      _ (wfRows_mulRows hacc (wfRows_letter' hG l (hw l List.mem_cons_self)))

theorem wfRows_wR' (hG : ZfGens) (w : List ℤ)
    (hw : ∀ l ∈ w, l ∈ letters) : wfRows (wR w) = true := by
  unfold wR wordRows
  exact wfRows_foldl_letters' hG w hw idRows wfRows_idRows

theorem wf_zfSeqR (hG : ZfGens) :
    ∀ s : List ℕ, (∀ g ∈ s, g < 3) → wfRows (zfSeqR s) = true
  | [], _ => wfRows_idRows
  | g :: s, hs => by
    change wfRows (mulRows (wR (zcGenWords.getD g [])) (zfSeqR s)) = true
    exact wfRows_mulRows (wfRows_wR' hG _ (zcGenWords_letters _ (zcGenWords_mem (hs g List.mem_cons_self))))
      (wf_zfSeqR hG s fun x hx => hs x (List.mem_cons_of_mem _ hx))

end CFSG.QuasithinUnique.A5

end
