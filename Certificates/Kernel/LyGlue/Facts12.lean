module

public import Certificates.Kernel.LyGlue.Facts2

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th

theorem invW_range {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    ∀ l ∈ McLMultiplier.invW w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  simp only [McLMultiplier.invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  omega

theorem uWordsInv_code {k : Nat} (hk : k < 4) :
    sel4 k (encW (McLMultiplier.invW Ly0.wordU1)) (encW (McLMultiplier.invW Ly0.wordU2))
      (encW (McLMultiplier.invW Ly0.wordU3)) (encW (McLMultiplier.invW Ly0.wordU4)) =
      encW (McLMultiplier.invW (Ly0.uWords.getD k [])) := by
  interval_cases k <;> rfl

theorem uPtInv (h : Ly0.tabCheck = true) {k : Nat} (hk : k < 4) (a : Fin Ly0.deg) :
    cdPt (uLen k) (sel4 k (encW (McLMultiplier.invW Ly0.wordU1))
      (encW (McLMultiplier.invW Ly0.wordU2)) (encW (McLMultiplier.invW Ly0.wordU3))
      (encW (McLMultiplier.invW Ly0.wordU4))) a = ((Ly0.uG k)⁻¹ a : Nat) := by
  have hlen : (McLMultiplier.invW (Ly0.uWords.getD k [])).length = uLen k := by
    rw [← uWords_len hk]
    simp [McLMultiplier.invW]
  rw [uWordsInv_code hk, ← hlen, cdPt_eq h _ (invW_range (uWords_range hk)),
    Ly0.wG_invW Ly0.gens0 (fun l hl => (uWords_range hk l hl).1), Ly0.uG_def]

theorem wptG_cons (G GI : Nat → Nat → Nat) (l : Int) (ws : List Int) (a : Nat) :
    wptG G GI (l :: ws) a = letPF G GI l (wptG G GI ws a) := rfl

theorem uwPt_eq (h : Ly0.tabCheck = true) :
    ∀ ws : List Int, (∀ l ∈ ws, l ≠ 0 ∧ l.natAbs ≤ 4) → ∀ a : Fin Ly0.deg,
      uwPt (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)
        (encW (McLMultiplier.invW Ly0.wordU1)) (encW (McLMultiplier.invW Ly0.wordU2))
        (encW (McLMultiplier.invW Ly0.wordU3)) (encW (McLMultiplier.invW Ly0.wordU4)) ws a =
        (wordG (wordLetter Ly0.uG) ws a : Nat)
  | [], _, a => rfl
  | l :: ws, hws, a => by
    have hl := hws l List.mem_cons_self
    have ih := uwPt_eq h ws (fun l' hl' => hws l' (List.mem_cons_of_mem _ hl'))
    rw [show wordG (wordLetter Ly0.uG) (l :: ws) =
      wordLetter Ly0.uG l * wordG (wordLetter Ly0.uG) ws by simp [wordG]]
    unfold uwPt
    rw [wptG_cons]
    have e : wptG (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2)
        (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
        (fun k a => cdPt (uLen k) (sel4 k (encW (McLMultiplier.invW Ly0.wordU1))
        (encW (McLMultiplier.invW Ly0.wordU2)) (encW (McLMultiplier.invW Ly0.wordU3))
        (encW (McLMultiplier.invW Ly0.wordU4))) a) ws a = (wordG (wordLetter Ly0.uG) ws a : Nat) :=
      ih a
    rw [e, Perm.mul_apply]
    unfold letPF wordLetter
    cases l with
    | ofNat k =>
      have h1 : k ≠ 0 := fun e => hl.1 (by rw [e]; rfl)
      have h2 : k ≤ 4 := hl.2
      have hk : 0 < (Int.ofNat k) := by rw [Int.ofNat_eq_coe]; omega
      rw [if_pos hk]
      exact uPt h (k := k - 1) (show k - 1 < 4 by omega) _
    | negSucc k =>
      have h2 : k + 1 ≤ 4 := hl.2
      have hk : ¬ 0 < Int.negSucc k := by rw [Int.negSucc_eq]; omega
      rw [if_neg hk]
      have e2 : (-Int.negSucc k).toNat - 1 = k := by rw [Int.negSucc_eq]; omega
      rw [e2]
      exact uPtInv h (by omega) _

theorem agree_spec : ∀ j < 5, ∀ k < 243,
    FT (uwPt (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)
        (encW (McLMultiplier.invW Ly0.wordU1)) (encW (McLMultiplier.invW Ly0.wordU2))
        (encW (McLMultiplier.invW Ly0.wordU3)) (encW (McLMultiplier.invW Ly0.wordU4))
        (Ly1080.txyWords.getD j []) (ST k)) =
      pg 8 (mask 8) (wprod 243 8 (mask 8) (letT GH.F ghInv) (Ly243.txyWords.getD j [])) k := by
  have h := k_agree
  simp only [CFSG.KS.PF.strictB_eqP] at h
  intro j hj k hk
  have h1 := allN_spec h j hj
  rw [CFSG.KS.PF.strictB_eqP] at h1
  exact Nat.eq_of_beq_eq_true (allN_spec h1 k hk)

end CertificateChecks.KernelLy

end
