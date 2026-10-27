module

public import CFSG.Monster.Existence.Census.CosetOneFusionInputs
public import Certificates.Kernel.MonsterExist.FusionWords
public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
public import CFSG.Monster.Existence.Census.FusionGensInputs

public section

namespace CertificateChecks.MonsterExist.Fusion

open CFSG.Monster.Existence.Census CFSG.Monster.B.TwoA.Census CFSG.Monster.B CFSG.Monster.B.Rep4371

@[expose] def imgsA : Array Model.Pauli := #[(false, 1, 60), (false, 2, 60), (false, 59, 3),
  (false, 55, 3), (false, 47, 3), (false, 31, 3), (true, 64, 128), (true, 128, 64),
  (true, 256, 512), (true, 512, 256), (false, 1024, 0), (false, 2048, 0), (false, 60, 61),
  (false, 60, 62), (false, 3, 56), (false, 3, 52), (false, 3, 44), (false, 3, 28), (false, 0, 64),
  (false, 0, 128), (false, 0, 256), (false, 0, 512), (false, 0, 1024), (false, 0, 2048)]

theorem imgs_one : imgs 1 = imgsA := by decide +kernel

@[expose] def walkA (w : List ℕ) (n : ℕ) : ℕ :=
  w.foldl (fun x k => Native.CosetEnum.act imgsA k x) n

@[expose] def walkOK (w : List ℕ) (r n : ℕ) : Bool := w.all (· < 24) && walkA w r == n

theorem exists_walk_of_walkOK {w : List ℕ} {r n : ℕ} (h : walkOK w r n = true) :
    ∃ w : List ℕ, w.all (· < 24) = true ∧ walkEnc w r = n := by
  rw [walkOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨w, h.1, by rw [walkEnc, imgs_one]; exact h.2⟩

@[expose] def fixOK : Bool :=
  (List.range 11).all fun j =>
    walkOK (fixWords.getD j ([], [])).1 (classEnc 0) (fusF (fusGen j) (fusShift j) (classEnc 0)) &&
      walkOK (fixWords.getD j ([], [])).2 (classEnc 4) (fusF (fusGen j) (fusShift j) (classEnc 4))

@[expose] def tgtOK (j : ℕ) : Bool :=
  (List.range 137).all fun k => decide (fusTarget j k < 137) &&
    walkOK ((tgtWords.getD j []).getD k []) (classEnc (fusTarget j k))
      (fusF (fusGen j) (fusShift j) (classEnc k))

theorem fix_of_fixOK (h : fixOK = true) : ∀ j < 11,
    (∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc 0) = fusF (fusGen j) (fusShift j) (classEnc 0)) ∧
    (∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc 4) = fusF (fusGen j) (fusShift j) (classEnc 4)) := by
  intro j hj
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [Bool.and_eq_true] at h1
  exact ⟨exists_walk_of_walkOK h1.1, exists_walk_of_walkOK h1.2⟩

theorem tgt_of_tgtOK {j : ℕ} (h : tgtOK j = true) : ∀ k < 137, fusTarget j k < 137 ∧
    ∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc (fusTarget j k)) = fusF (fusGen j) (fusShift j) (classEnc k) := by
  intro k hk
  have h1 := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨h1.1, exists_walk_of_walkOK h1.2⟩

end CertificateChecks.MonsterExist.Fusion
