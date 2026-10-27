module

public import Certificates.Kernel.SporSch.Ly.FiveClassChk
public import Certificates.Kernel.SporSch.Ly.FiveLanes
public import Certificates.Kernel.SporSch.Ly.Seven2189

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFC

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySev
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CertificateChecks.KernelSporSch.LySvF
open CertificateChecks.KernelSporSch.LySv CertificateChecks.KernelSporSch.LyFL
open CFSG.RankThree.PartOne.LyFive CFSG.RankThree.Native

local notation "U" X:max => unpackL 111 12 1332 X

theorem tw_eq (w : List Int) :
    evalWordM seedM (seedMInv (U B4)) w = U (TW w) ∧ vld (TW w) = true :=
  word_of hgS hgiS vGS vGSI w

theorem classT_eq (τ : List Int) : classT τ = U (TW τ) := by
  unfold classT classB4
  rw [b4_eq]
  exact (tw_eq τ).1

theorem classT_inv {τ : List Int} (h : Nat.beq (mul (TW τ) (TW (invW τ))) ONE = true) :
    invM 5 111 (classT τ) = U (TW (invW τ)) := by
  rw [classT_eq]
  exact invM_eq Nat.prime_five consts (hv (tw_eq τ).2) (hv (tw_eq (invW τ)).2) h

theorem classT_check {τ : List Int} (h : Nat.beq (mul (TW τ) (TW (invW τ))) ONE = true) :
    (mulM 5 111 (classT τ) (invM 5 111 (classT τ)) == idM 111) = true := by
  rw [classT_inv h, classT_eq, mulE (tw_eq τ).2 (tw_eq (invW τ)).2, idE,
    beqE (mulV (tw_eq τ).2 (tw_eq (invW τ)).2) vOne]
  exact h

theorem classR_eq {τ : List Int} {W : Nat} (hW : vld W = true) {R : Array Nat}
    (ht : Nat.beq (mul (TW τ) (TW (invW τ))) ONE = true)
    (hr : rOK (mul (mul (TW (invW τ)) W) (TW τ)) R = true) (hs : R.size = 49) :
    classR (U W) τ = R := by
  unfold classR
  have v1 := (tw_eq τ).2
  have v2 := (tw_eq (invW τ)).2
  rw [classT_inv ht, classT_eq, mulE v2 hW, mulE (mulV v2 hW) v1,
    restr_eq consts (hv (mulV (mulV v2 hW) v1)) (hv vUP) up_eq]
  exact ofFn_of_rOK hr hs

theorem yArr_eq : lyFiveYArr = U YY ∧ vld YY = true := by
  obtain ⟨e0, v0⟩ := v_eq 0
  obtain ⟨e1, v1⟩ := v_eq 1
  refine ⟨?_, mulV v0 v1⟩
  unfold lyFiveYArr
  rw [show (0 : ℕ) = (0 : Fin 4).val from rfl, e0, show (1 : ℕ) = (1 : Fin 4).val from rfl, e1,
    mulE v0 v1]
  rfl

theorem classR_x : classR lyFiveXArr xWord = ⟨CertificateChecks.KernelLyFive.D.RX⟩ := by
  rw [x_eq]
  exact classR_eq vXX tx rx (by decide +kernel)

theorem classR_y3 : classR lyFiveYArr y3Word = ⟨CertificateChecks.KernelLyFive.D.RY3⟩ := by
  rw [yArr_eq.1]
  exact classR_eq yArr_eq.2 ty3 ry3 (by decide +kernel)

theorem classR_y1 : classR lyFiveYArr y1Word = ⟨CertificateChecks.KernelLyFive.D.RY1⟩ := by
  rw [yArr_eq.1]
  exact classR_eq yArr_eq.2 ty1 ry1 (by decide +kernel)

theorem nfArr_eq (c : ℕ) (e : List ℕ) : nfArr c e = U (nfE c e) ∧ vld (nfE c e) = true :=
  nf_eq (c % 5) fun j => e.getD j.val 0 % 5

theorem lyYComm : lyYCommOK = true := by
  obtain ⟨ey, vy⟩ := yArr_eq
  have h1 : ∀ d : List ℤ × ℕ × List ℕ,
      (let D := mulM 5 111 (fiveWordArr d.1) (nfArr d.2.1 d.2.2)
       mulM 5 111 D lyFiveYArr == mulM 5 111 lyFiveYArr D) =
      Nat.beq (mul (mul (wordL d.1) (nfE d.2.1 d.2.2)) YY) (mul YY (mul (wordL d.1) (nfE d.2.1 d.2.2))) := by
    intro d
    obtain ⟨ew, vw⟩ := word_eq d.1
    obtain ⟨en, vn⟩ := nfArr_eq d.2.1 d.2.2
    simp only []
    rw [ew, en, ey, mulE vw vn, mulE (mulV vw vn) vy, mulE vy (mulV vw vn),
      beqE (mulV (mulV vw vn) vy) (mulV vy (mulV vw vn))]
  have h2 : ∀ u : List ℕ,
      (let F := nfArr 0 u
       mulM 5 111 F lyFiveYArr == mulM 5 111 lyFiveYArr F) =
      Nat.beq (mul (nfE 0 u) YY) (mul YY (nfE 0 u)) := by
    intro u
    obtain ⟨en, vn⟩ := nfArr_eq 0 u
    simp only []
    rw [en, ey, mulE vn vy, mulE vy vn, beqE (mulV vn vy) (mulV vy vn)]
  have hc := comm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  unfold lyYCommOK
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun d hd => (h1 d).trans (hc.1 d hd), fun u hu => (h2 u).trans (hc.2 u hu)⟩

end CertificateChecks.KernelSporSch.LyFC

end
