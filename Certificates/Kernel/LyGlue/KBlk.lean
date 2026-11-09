module

public import Certificates.Kernel.LyGlue.PtDefs
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def lyBody (n ng wH : Nat) (F : Nat → Nat) (gpt : Nat → Nat → Nat)
    (H : Nat → Nat) (a : Nat) : Bool :=
  strictB (F a) (fun v => bIf(Nat.beq v (nat_lit 65535), true,
    bAnd(Nat.blt v n, allN ng (fun k => Nat.beq (F (gpt k a)) (pg wH (mask wH) (H k) v)))))

theorem ly_blkOK_eq (deg n ng wH : Nat) (F : Nat → Nat) (gpt : Nat → Nat → Nat) (H : Nat → Nat) :
    blkOK deg n ng wH F gpt H = allN deg (lyBody n ng wH F gpt H) := rfl

theorem ly_sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem ly_allBlk_spec {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (Nat.add b l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true at h
    cases e : f (Nat.add b len) with
    | false =>
      rw [e] at h
      exact absurd h Bool.false_ne_true
    | true =>
      rw [e] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ly_allBlk_spec h l hl
      · exact e

theorem k_yBlk0 : allBlk (Nat.mul 7425 0) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk1 : allBlk (Nat.mul 7425 1) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk2 : allBlk (Nat.mul 7425 2) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk3 : allBlk (Nat.mul 7425 3) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk4 : allBlk (Nat.mul 7425 4) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk5 : allBlk (Nat.mul 7425 5) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk6 : allBlk (Nat.mul 7425 6) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk7 : allBlk (Nat.mul 7425 7) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk8 : allBlk (Nat.mul 7425 8) (lyBody 1080 4 11 FY
    (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
    UH.F) 7425 = true := by quickRfl

theorem k_yBlk : (strictB (encW Ly0.wordU1) fun e0 => strictB (encW Ly0.wordU2) fun e1 =>
    strictB (encW Ly0.wordU3) fun e2 => strictB (encW Ly0.wordU4) fun e3 =>
    yBlkK e0 e1 e2 e3) = true := by
  simp only [ly_sB]
  unfold yBlkK
  rw [ly_blkOK_eq]
  have P : ∀ i < 9, allBlk (Nat.mul 7425 i) (lyBody 1080 4 11 FY
      (fun k a => cdPt (uLen k) (sel4 k (encW Ly0.wordU1) (encW Ly0.wordU2) (encW Ly0.wordU3) (encW Ly0.wordU4)) a)
      UH.F) 7425 = true := by
    intro i hi
    interval_cases i
    exacts [k_yBlk0, k_yBlk1, k_yBlk2, k_yBlk3, k_yBlk4, k_yBlk5, k_yBlk6, k_yBlk7, k_yBlk8]
  refine CFSG.KC.BfsPin.allN_intro fun a ha => ?_
  have hb := ly_allBlk_spec (P (a / 7425) (by omega)) (a % 7425) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 7425 (a / 7425)) (a % 7425) = a := by
    show 7425 * (a / 7425) + a % 7425 = a
    omega
  rw [e] at hb
  exact hb

theorem k_tBlk : (strictB (encW (Glue.txWords.getD 0 [])) fun e0 =>
    strictB (encW (Glue.txWords.getD 1 [])) fun e1 =>
    strictB (encW (Glue.txWords.getD 2 [])) fun e2 =>
    strictB (encW (Glue.txWords.getD 3 [])) fun e3 =>
    tBlkK e0 e1 e2 e3) = true := by
  decide +kernel

theorem k_neg : (strictB (encW Ly0.wordU2) fun e1 => strictB (encW Ly0.wordU3) fun e2 =>
    strictB (encW Ly0.wordU4) fun e3 => yBlkK e1 e1 e2 e3) = false := by
  decide +kernel

end CertificateChecks.KernelLy

end
