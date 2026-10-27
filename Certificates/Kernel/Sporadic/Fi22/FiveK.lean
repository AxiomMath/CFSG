module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22FiveK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W

@[expose] noncomputable def pwK (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 3510 12) (fun _ acc => Fi22X.c p acc) k

@[expose] noncomputable def planeK (X Y i j : Nat) : Nat := Fi22X.c (pwK X i) (pwK Y j)

@[expose] noncomputable def nProdK (N1 N2 : Nat) (w : List Nat) : Nat :=
  w.foldr (fun k A => Fi22X.c (if k = 1 then N1 else N2) A) (pidn 3510 12)

@[expose] noncomputable def conjK (X Y N1 N2 : Nat) (t : Nat × Nat × List Nat) : Bool :=
  strictB (nProdK N1 N2 t.2.2) fun P =>
    Nat.beq (Fi22X.c P X) (Fi22X.c (planeK X Y t.1 t.2.1) P)

@[expose] noncomputable def orbK (X Y N1 N2 : Nat) : Bool :=
  Fi22X.cn X && Fi22X.cn Y && Fi22X.cn N1 && Fi22X.cn N2 &&
  Nat.beq (pwK X 5) (pidn 3510 12) && Nat.beq (pwK Y 5) (pidn 3510 12) &&
  Nat.beq (Fi22X.c X Y) (Fi22X.c Y X) &&
  allN 5 (fun i => allN 5 fun j => (i == 0 && j == 0) || !(Nat.beq (planeK X Y i j) (pidn 3510 12))) &&
  Nat.beq (Fi22X.c N1 X) (Fi22X.c (planeK X Y 2 3) N1) &&
  Nat.beq (Fi22X.c N1 Y) (Fi22X.c (planeK X Y 1 2) N1) &&
  Nat.beq (Fi22X.c N2 X) (Fi22X.c (planeK X Y 4 1) N2) &&
  Nat.beq (Fi22X.c N2 Y) (Fi22X.c (planeK X Y 1 1) N2) &&
  allN 5 (fun i => allN 5 fun j => (i == 0 && j == 0) ||
    conjWords.any fun t => t.1 == i && t.2.1 == j && conjK X Y N1 N2 t)

@[expose] noncomputable def genK (X Y H N1 N2 Z : Nat) : Bool :=
  Fi22X.cn X && Fi22X.cn Y && Fi22X.cn H && Fi22X.cn N1 && Fi22X.cn N2 && Fi22X.cn Z &&
  permOK 3510 12 (mask 12) (3510 * 12) X (Fi22X.inv X) &&
  permOK 3510 12 (mask 12) (3510 * 12) Y (Fi22X.inv Y) &&
  permOK 3510 12 (mask 12) (3510 * 12) H (Fi22X.inv H) &&
  permOK 3510 12 (mask 12) (3510 * 12) N1 (Fi22X.inv N1) &&
  permOK 3510 12 (mask 12) (3510 * 12) N2 (Fi22X.inv N2) &&
  permOK 3510 12 (mask 12) (3510 * 12) Z (Fi22X.inv Z) &&
  Nat.beq (Fi22X.c Z X) (Fi22X.c (pwK X 2) Z)

@[expose] noncomputable def allOrb : Bool :=
  strictB (W (signedWord wx)) fun X => strictB (W (signedWord wy)) fun Y =>
    strictB (W nw1) fun N1 => strictB (W nw2) fun N2 => orbK X Y N1 N2

@[expose] noncomputable def allGen : Bool :=
  strictB (W (signedWord wx)) fun X => strictB (W (signedWord wy)) fun Y =>
    strictB (W hw) fun H => strictB (W nw1) fun N1 => strictB (W nw2) fun N2 =>
      strictB (W zw) fun Z => genK X Y H N1 N2 Z

theorem orbOK : allOrb = true := by quickRfl

theorem genOK : allGen = true := by quickRfl

theorem lettersOK' : (signedWord wx :: signedWord wy :: nw1 :: nw2 :: hw :: [zw]).all
    (lettersK 2) = true := by quickRfl

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem pw_eq {p : Nat} (hp : Fi22X.cn p = true) :
    ∀ k, pw (unpack 3510 12 p) k = unpack 3510 12 (pwK p k) ∧ Fi22X.cn (pwK p k) = true
  | 0 => ⟨(idK_sound idOK).symm, cnId⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := pw_eq hp k
    have e : pw (unpack 3510 12 p) (k + 1) = compA 3510 (unpack 3510 12 p) (pw (unpack 3510 12 p) k) :=
      rfl
    have e2 : pwK p (k + 1) = Fi22X.c p (pwK p k) := rfl
    rw [e, e2, ih1, Fi22X.comp_eq hp ih2]
    exact ⟨rfl, Fi22X.cn_c hp ih2⟩

theorem hI : idA 3510 = unpack 3510 12 (pidn 3510 12) := (idK_sound idOK).symm

theorem comp_beq {p q r s : Nat} (hp : Fi22X.cn p = true) (hq : Fi22X.cn q = true)
    (hr : Fi22X.cn r = true) (hs : Fi22X.cn s = true) :
    eqA 3510 (compA 3510 (unpack 3510 12 p) (unpack 3510 12 q))
      (compA 3510 (unpack 3510 12 r) (unpack 3510 12 s)) =
      Nat.beq (Fi22X.c p q) (Fi22X.c r s) := by
  rw [Fi22X.comp_eq hp hq, Fi22X.comp_eq hr hs]
  exact eqA_unpack (Fi22X.cn_c hp hq) (Fi22X.cn_c hr hs)

section Sound

variable {X Y N1 N2 : Nat} (hX : xA = unpack 3510 12 X) (hY : yA = unpack 3510 12 Y)
  (h1 : n1A = unpack 3510 12 N1) (h2 : n2A = unpack 3510 12 N2)
  (cX : Fi22X.cn X = true) (cY : Fi22X.cn Y = true) (c1 : Fi22X.cn N1 = true)
  (c2 : Fi22X.cn N2 = true)
include hX hY cX cY

theorem plane_eq (i j : Nat) :
    planeA i j = unpack 3510 12 (planeK X Y i j) ∧ Fi22X.cn (planeK X Y i j) = true := by
  obtain ⟨a1, a2⟩ := pw_eq cX i
  obtain ⟨b1, b2⟩ := pw_eq cY j
  unfold planeA planeK
  rw [hX, hY, a1, b1, Fi22X.comp_eq a2 b2]
  exact ⟨rfl, Fi22X.cn_c a2 b2⟩

omit hX hY cX cY in
include h1 h2 c1 c2 in
theorem nProd_eq : ∀ w : List Nat,
    nProd w = unpack 3510 12 (nProdK N1 N2 w) ∧ Fi22X.cn (nProdK N1 N2 w) = true
  | [] => ⟨hI, cnId⟩
  | k :: w => by
    obtain ⟨ih1, ih2⟩ := nProd_eq w
    have e : nProd (k :: w) = compA 3510 (if k = 1 then n1A else n2A) (nProd w) := rfl
    have e2 : nProdK N1 N2 (k :: w) = Fi22X.c (if k = 1 then N1 else N2) (nProdK N1 N2 w) := rfl
    rw [e, e2, ih1]
    by_cases hk : k = 1
    · rw [if_pos hk, if_pos hk, h1, Fi22X.comp_eq c1 ih2]
      exact ⟨rfl, Fi22X.cn_c c1 ih2⟩
    · rw [if_neg hk, if_neg hk, h2, Fi22X.comp_eq c2 ih2]
      exact ⟨rfl, Fi22X.cn_c c2 ih2⟩

include h1 h2 c1 c2 in
theorem conj_eq (t : Nat × Nat × List Nat) : conjOK t = conjK X Y N1 N2 t := by
  obtain ⟨p1, p2⟩ := nProd_eq h1 h2 c1 c2 t.2.2
  obtain ⟨q1, q2⟩ := plane_eq hX hY cX cY t.1 t.2.1
  unfold conjOK conjK
  rw [strictB_eq', p1, q1, hX, Fi22X.comp_eq p2 cX, Fi22X.comp_eq q2 p2]
  exact eqA_unpack (Fi22X.cn_c p2 cX) (Fi22X.cn_c q2 p2)

include h1 h2 c1 c2 in
theorem orb_of (hl : (lettersOK 2 (signedWord wx) && lettersOK 2 (signedWord wy) &&
      lettersOK 2 nw1 && lettersOK 2 nw2) = true)
    (h : orbK X Y N1 N2 = true) : orbCheck = true := by
  unfold orbK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, -, -, k5, k6, k7, k8, k9, k10, k11, k12, k13⟩ := h
  simp only [Bool.and_eq_true, and_assoc] at hl
  obtain ⟨l1, l2, l3, l4⟩ := hl
  obtain ⟨x5, cx5⟩ := pw_eq cX 5
  obtain ⟨y5, cy5⟩ := pw_eq cY 5
  have pl := plane_eq hX hY cX cY
  unfold orbCheck
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨l1, l2, l3, l4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hX, x5, hI, eqA_unpack cx5 cnId]
    exact k5
  · rw [hY, y5, hI, eqA_unpack cy5 cnId]
    exact k6
  · unfold commA
    rw [hX, hY, comp_beq cX cY cY cX]
    exact k7
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have k := allN_spec (allN_spec k8 i hi) j hj
    rw [(pl i j).1, hI, eqA_unpack (pl i j).2 cnId]
    exact k
  · rw [h1, hX, (pl 2 3).1, comp_beq c1 cX (pl 2 3).2 c1]
    exact k9
  · rw [h1, hY, (pl 1 2).1, comp_beq c1 cY (pl 1 2).2 c1]
    exact k10
  · rw [h2, hX, (pl 4 1).1, comp_beq c2 cX (pl 4 1).2 c2]
    exact k11
  · rw [h2, hY, (pl 1 1).1, comp_beq c2 cY (pl 1 1).2 c2]
    exact k12
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have k := allN_spec (allN_spec k13 i hi) j hj
    simp only [conj_eq hX hY h1 h2 cX cY c1 c2]
    exact k

end Sound

theorem orb_parts : orbK (W (signedWord wx)) (W (signedWord wy)) (W nw1) (W nw2) = true := by
  have h := orbOK
  unfold allOrb at h
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq'] at h
  exact h

theorem gen_parts : genK (W (signedWord wx)) (W (signedWord wy)) (W hw) (W nw1) (W nw2) (W zw) =
    true := by
  have h := genOK
  unfold allGen at h
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq', strictB_eq'] at h
  exact h

theorem letters : lettersK 2 (signedWord wx) = true ∧ lettersK 2 (signedWord wy) = true ∧
    lettersK 2 nw1 = true ∧ lettersK 2 nw2 = true ∧ lettersK 2 hw = true ∧
    lettersK 2 zw = true := by
  have h := lettersOK'
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact h

theorem eval_eq {w : List Int} (hl : lettersK 2 w = true) : evalW w = unpack 3510 12 (W w) :=
  word_eq orig_bind hl

theorem x_eq : xA = unpack 3510 12 (W (signedWord wx)) := eval_eq letters.1
theorem y_eq : yA = unpack 3510 12 (W (signedWord wy)) := eval_eq letters.2.1
theorem n1_eq : n1A = unpack 3510 12 (W nw1) := eval_eq letters.2.2.1
theorem n2_eq : n2A = unpack 3510 12 (W nw2) := eval_eq letters.2.2.2.1
theorem h_eq : hA = unpack 3510 12 (W hw) := eval_eq letters.2.2.2.2.1
theorem z_eq : zA = unpack 3510 12 (W zw) := eval_eq letters.2.2.2.2.2

theorem orbK_cn {X Y N1 N2 : Nat} (h : orbK X Y N1 N2 = true) :
    Fi22X.cn X = true ∧ Fi22X.cn Y = true ∧ Fi22X.cn N1 = true ∧ Fi22X.cn N2 = true := by
  unfold orbK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem orb : orbCheck = true := by
  have h := orb_parts
  obtain ⟨cX, cY, c1, c2⟩ := orbK_cn h
  exact orb_of x_eq y_eq n1_eq n2_eq cX cY c1 c2 (by decide +kernel) h

theorem gen_of {X Y H N1 N2 Z : Nat} (hX : xA = unpack 3510 12 X) (hY : yA = unpack 3510 12 Y)
    (hH : hA = unpack 3510 12 H) (h1 : n1A = unpack 3510 12 N1) (h2 : n2A = unpack 3510 12 N2)
    (hZ : zA = unpack 3510 12 Z) (h : genK X Y H N1 N2 Z = true) : genCheck = true := by
  unfold genK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨cX, -, -, -, -, cZ, pX, pY, pH, p1, p2, pZ, kz⟩ := h
  obtain ⟨x2, cx2⟩ := pw_eq cX 2
  have hInv : ∀ k < 6, isInvA 3510 gens6A[k]! gens6Inv[k]! = true := by
    intro k hk
    have e : gens6Inv[k]! = invCand 3510 gens6A[k]! := by
      rw [getElem!_pos _ k (by simp [gens6Inv, gens6A]; omega),
        getElem!_pos gens6A k (by simp [gens6A]; omega)]
      simp [gens6Inv]
    rw [e]
    interval_cases k
    · have e0 : gens6A[0]! = xA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hX pX
    · have e0 : gens6A[1]! = yA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hY pY
    · have e0 : gens6A[2]! = hA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hH pH
    · have e0 : gens6A[3]! = n1A := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of h1 p1
    · have e0 : gens6A[4]! = n2A := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of h2 p2
    · have e0 : gens6A[5]! = zA := by simp [gens6A]
      rw [e0]
      exact Fi22E2067.isInv_of hZ pZ
  have hz : eqA 3510 (compA 3510 zA xA) (compA 3510 (pw xA 2) zA) = true := by
    rw [hX, hZ, x2, comp_beq cZ cX cx2 cZ]
    exact kz
  have hl : (lettersOK 2 zw && lettersOK 6 g1w && lettersOK 6 g2w) = true := by decide +kernel
  simp only [Bool.and_eq_true] at hl
  unfold genCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨hl.1.1, hz⟩, hl.1.2⟩, hl.2⟩, CFSG.Monster.B.Co2.allLt_iff.2 hInv⟩

theorem gen : genCheck = true := gen_of x_eq y_eq h_eq n1_eq n2_eq z_eq gen_parts

end CertificateChecks.KernelSpor.Fi22FiveK

end
