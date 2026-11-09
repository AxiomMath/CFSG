module

public import Certificates.Kernel.Tc.HeKDefs
public import Certificates.Kernel.Tc.HeChk
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.TcF
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CertificateChecks.KernelTc.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
  CertificateChecks.KernelLC.HeFix

theorem wordK_append {n w m : Nat} {S SI : Nat → Nat} (idn : Nat) (u v : List Int) :
    wordK n w m idn S SI (u ++ v) = wordK n w m (wordK n w m idn S SI v) S SI u := by
  induction u with
  | nil => rfl
  | cons z u ih =>
    unfold wordK at ih ⊢
    dsimp only [List.cons_append]
    rw [ih]

theorem wordK_drop {n w m : Nat} {S SI : Nat → Nat} (idn : Nat) (L : List Int) (a c : Nat) :
    wordK n w m idn S SI (L.drop a) =
      wordK n w m (wordK n w m idn S SI (L.drop (a + c))) S SI ((L.drop a).take c) := by
  conv_lhs => rw [← List.take_append_drop c (L.drop a)]
  rw [wordK_append, List.drop_drop]

theorem wordK_chunks {n w m : Nat} {S SI : Nat → Nat} (idn c : Nat) (L : List Int) (H : Nat → Nat)
    (r : Nat) (hl : L.length ≤ c * r) (hr : H r = idn)
    (hc : ∀ j < r, wordK n w m (H (j + 1)) S SI ((L.drop (c * j)).take c) = H j) :
    wordK n w m idn S SI L = H 0 := by
  have key : ∀ i, i ≤ r → wordK n w m idn S SI (L.drop (c * (r - i))) = H (r - i) := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hl, hr]
      rfl
    | succ i ih =>
      intro hi
      have hj : r - (i + 1) < r := by omega
      have e1 : c * (r - (i + 1)) + c = c * (r - i) := by
        rw [show r - i = r - (i + 1) + 1 by omega, Nat.mul_succ]
      have e2 : r - (i + 1) + 1 = r - i := by omega
      rw [wordK_drop idn L (c * (r - (i + 1))) c, e1, ih (by omega), ← e2]
      exact hc _ hj
  simpa using key r le_rfl

@[expose] noncomputable def ck (k j : Nat) : Nat := HC (Nat.add (Nat.mul 10 k) j)

@[expose] noncomputable def chK (k j : Nat) : Bool :=
  Nat.beq
    (wordK 8330 14 (mask 14) (ck k (j + 1)) L2 L2I (((heTcWs.getD k []).drop (48 * j)).take 48))
    (ck k j)

@[expose] noncomputable def endK (k r : Nat) : Bool :=
  bAnd(Nat.ble (heTcWs.getD k []).length (48 * r), bAnd(Nat.beq (ck k 0) (HT k),
    bAnd(Nat.beq (ck k r) (pidn 8330 14), bAnd(szOK 8330 14, lettersK 2 (heTcWs.getD k [])))))

theorem wOK_of {k r : Nat} (he : endK k r = true)
    (hi : invEqK 8330 14 (mask 14) (8330 * 14) (HT k) (HTI k) = true)
    (hc : ∀ j < r, chK k j = true) : wOK k = true := by
  unfold endK at he
  simp only [bAnd_iff] at he
  obtain ⟨hl, h0, hr, hs, hlt⟩ := he
  have hw := wordK_chunks (n := 8330) (w := 14) (m := mask 14) (S := L2) (SI := L2I) (pidn 8330 14)
    48 (heTcWs.getD k []) (ck k) r (Nat.le_of_ble_eq_true hl) (Nat.eq_of_beq_eq_true hr)
    (fun j hj => Nat.eq_of_beq_eq_true (hc j hj))
  unfold wOK wordEqK
  simp only [bAnd_iff]
  refine ⟨⟨hs, hlt, ?_⟩, hi⟩
  rw [hw, Nat.eq_of_beq_eq_true h0]
  exact Nat.beq_refl _

end CertificateChecks.KernelTc.He

end
