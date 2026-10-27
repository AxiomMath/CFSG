module

public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsCert
public import Certificates.Data.Kernel.U6.Pack
import CFSG.Certificates.Kernel.U6LinProved
import CFSG.Certificates.Kernel.Common.Cover
public import Mathlib

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (formGen formBlock formFb formCheckW formsCheckW
  formQcols id16 btr unpackN packN)

@[expose] noncomputable def formBlockK (G GT : List ℕ) (X k : ℕ) : ℕ :=
  nIf(Nat.beq k 0, Nat.xor X (trK 16 X),
    nIf(Nat.beq k 1, Nat.land X (idF 16),
      Nat.xor (mulF 16 (mulF 16 (getLD 0 GT (k - 2)) X) (getLD 0 G (k - 2))) X))

@[expose] noncomputable def formFbK (G GT : List ℕ) (v : ℕ) : ℕ :=
  orN 12 fun k => Nat.shiftLeft (formBlockK G GT (fget v 0 256) k) (Nat.mul k 256)

theorem packM_id16 : packM 16 id16 = idF 16 := by decide +kernel

theorem formFb_eq {z : ℕ} {G GT : List ℕ}
    (hG : ∀ k < 10, packM 16 (formGen z k) = getLD 0 G k)
    (hGT : ∀ k < 10, packM 16 (btr 16 16 (formGen z k)) = getLD 0 GT k) (v : ℕ) :
    formFb z v = formFbK G GT v := by
  rw [formFb, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  congr 1
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | h2
  · rw [formBlock, ite_eq_left_of_eq_true _ _ (eq_true rfl), packM_bxor_proved, packM_btr_proved,
      packM_unpackN_proved]
    rfl
  · rw [formBlock, ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      ite_eq_left_of_eq_true _ _ (eq_true rfl), packM_diag16_proved, packM_unpackN_proved,
      packM_id16]
    rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [formBlock, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel, packM_bxor_proved,
      packM_bmul_proved, packM_bmul_proved, packM_unpackN_proved, hG j (by omega),
      hGT j (by omega)]
    rfl

@[expose] noncomputable def formSeg (z i : ℕ) : Bool :=
  idRowsSeg 256 [] (formQcols z).toList ((List.range' (1 * i) 1).map fun l =>
      formFbK (getLD [] formGL (z - 4)) (getLD [] formGTL (z - 4)) (2 ^ l))
    (((List.replicate 256 0).drop (1 * i)).take 1) (1 * i)

theorem formCheckW_of {z : ℕ}
    (hG : ∀ k < 10, packM 16 (formGen z k) = getLD 0 (getLD [] formGL (z - 4)) k)
    (hGT : ∀ k < 10, packM 16 (btr 16 16 (formGen z k)) = getLD 0 (getLD [] formGTL (z - 4)) k)
    (hp : (formQcols z).size = 12 * 256) (h : ∀ i < 256, formSeg z i = true) :
    formCheckW z = true :=
  injCheckWith_of_idRowsK_proved (fun l hl => by rw [getLD_map_range _ _ hl, formFb_eq hG hGT]) hp
    (idRowsK_of_segs_proved (c := 1) (k := 256) _ rfl h (List.length_replicate ..))

set_option maxRecDepth 100000

theorem formCheckW_4 : formCheckW 4 = true :=
  formCheckW_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by kc_cover 1)

theorem formCheckW_5 : formCheckW 5 = true :=
  formCheckW_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by kc_cover 1)

theorem formCheckW_6 : formCheckW 6 = true :=
  formCheckW_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by kc_cover 1)

theorem formCheckW_7 : formCheckW 7 = true :=
  formCheckW_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by kc_cover 1)

theorem formsCheckW_true : formsCheckW = true := by
  rw [formsCheckW, formCheckW_4, formCheckW_5, formCheckW_6, formCheckW_7]
  rfl

end CertificateChecks.KernelU6
