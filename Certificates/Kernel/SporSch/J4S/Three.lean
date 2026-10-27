
module

public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.J4S.XY
public import CFSG.Certificates.Kernel.SporSch.J4STokSound
public import CFSG.Certificates.Kernel.Spor.Loops
meta import CFSG.Sporadic.Schreier.J4SThreeDataInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.J4Q3T CFSG.Sporadic.J4Schreier.q3WordsText

#kss_tokens CertificateChecks.KernelSporSch.J4Q3T CFSG.Sporadic.J4Schreier.q3WordsText

#kss_words CertificateChecks.KernelSporSch.J4Q3T CFSG.Sporadic.J4Schreier.q3WordsText 2

#kss_table CertificateChecks.KernelSporSch.J4Q3C CFSG.Sporadic.J4Schreier.q3Cols 11 11

#kss_table CertificateChecks.KernelSporSch.J4Q3P CFSG.Sporadic.J4Schreier.q3Par 5 2

#kss_table CertificateChecks.KernelSporSch.J4Q3E CFSG.Sporadic.J4Schreier.q3Edges 5 2

namespace CertificateChecks.KernelSporSch.J4Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.Schreier.PairText CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

theorem beq_ne {k : Nat} (h : 0 < k) : Nat.beq k 0 = false :=
  Bool.eq_false_iff.2 fun e => by have := Nat.eq_of_beq_eq_true e; omega

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem words_eq : q3Words = J4Q3T.ws.toArray := by
  rw [q3Words, J4Q3T.eq, CFSG.KS.SporSch.tokK_sound J4Q3T.tok]
  exact tokWords_sound J4Q3T.wtok

theorem pow4 (C : Array ℕ) : powCols C 4 = comp11 (comp11 (comp11 C C) (comp11 C C))
    (idRows 11) := by
  rw [powCols, ite_eq_right (by decide), ite_eq_right (by decide), powCols, ite_eq_right (by decide),
    ite_eq_right (by decide), powCols, ite_eq_right (by decide), ite_eq_left (by decide), powCols, ite_eq_left rfl]

theorem pow2 (C : Array ℕ) : powCols C 2 = comp11 (comp11 C C) (idRows 11) := by
  rw [powCols, ite_eq_right (by decide), ite_eq_right (by decide), powCols, ite_eq_right (by decide),
    ite_eq_left (by decide), powCols, ite_eq_left rfl]

theorem gen0 : Nat.beq (compK (compK (compK (W J4Q3T.w0) (W J4Q3T.w0))
    (compK (W J4Q3T.w0) (W J4Q3T.w0))) pidK) (J4Q3C 1) = true := by quickRfl

theorem gen1 : Nat.beq (compK (compK (W J4Q3T.w1) (W J4Q3T.w1)) pidK) (J4Q3C 2) = true := by
  quickRfl

theorem par : allN 27 (fun k => bIf(Nat.beq k 0, true,
    bAnd(Nat.blt (ent 5 (J4Q3P k) 0) k, bAnd(Nat.blt (ent 5 (J4Q3P k) 1) 2,
      Nat.beq (compK (J4Q3C (ent 5 (J4Q3P k) 0)) (J4Q3C (Nat.add (ent 5 (J4Q3P k) 1) 1)))
        (J4Q3C k))))) = true := by quickRfl

theorem edge : allN 27 (fun k => allN 2 (fun g => bAnd(Nat.blt (ent 5 (J4Q3E k) g) 27,
    Nat.beq (compK (J4Q3C k) (J4Q3C (Nat.add g 1))) (J4Q3C (ent 5 (J4Q3E k) g))))) = true := by
  quickRfl

theorem zero : Nat.beq pidK (J4Q3C 0) = true := by quickRfl

theorem dist : allN 27 (fun k => allN k (fun k' =>
    bAnd(canonK (J4Q3C k'), bAnd(canonK (J4Q3C k), Bool.not (Nat.beq (J4Q3C k') (J4Q3C k)))))) =
    true := by quickRfl

theorem fix : allN 27 (fun k => bIf(Nat.beq k 0, true, Nat.ble (fixCntK (J4Q3C k)) 32)) = true := by
  quickRfl

theorem C_eq {k : Nat} (hk : k < 27) : q3Cols[k]! = unpack11 (J4Q3C k) :=
  (bind2_sound J4Q3C.bind).2 k hk

theorem P_get {k i : Nat} (hk : k < 27) (hi : i < 2) : (q3Par[k]!)[i]! = ent 5 (J4Q3P k) i := by
  rw [(bind2_sound J4Q3P.bind).2 k hk, unpackW_get hi]

theorem E_get {k i : Nat} (hk : k < 27) (hi : i < 2) : (q3Edges[k]!)[i]! = ent 5 (J4Q3E k) i := by
  rw [(bind2_sound J4Q3E.bind).2 k hk, unpackW_get hi]

theorem w_get0 : q3Words[0]! = J4Q3T.w0 := by rw [words_eq]; rfl

theorem w_get1 : q3Words[1]! = J4Q3T.w1 := by rw [words_eq]; rfl

theorem facts : (∀ i < 2, powCols (wordCols q3Words[i]!) q3Exps[i]! = q3Cols[i + 1]!)
    ∧ (∀ k < 27, (q3Cols[k]!).size = 11 ∧ (∀ j < 11, (q3Cols[k]!)[j]! < 2048) ∧
      (0 < k → (q3Par[k]!)[0]! < k ∧ (q3Par[k]!)[1]! < 2 ∧
        q3Cols[k]! = comp11 q3Cols[(q3Par[k]!)[0]!]! q3Cols[(q3Par[k]!)[1]! + 1]!) ∧
      ∀ g < 2, (q3Edges[k]!)[g]! < 27 ∧
        q3Cols[(q3Edges[k]!)[g]!]! = comp11 q3Cols[k]! q3Cols[g + 1]!)
    ∧ (q3Cols[0]! = idRows 11)
    ∧ (∀ k < 27, ∀ k' < k, q3Cols[k']! ≠ q3Cols[k]!)
    ∧ (∀ k < 27, 0 < k → fixCount q3Cols[k]! ≤ 32) := by
  refine ⟨fun i hi => ?_, fun k hk => ?_, ?_, fun k hk k' hk' => ?_, fun k hk hk0 => ?_⟩
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [w_get0, C_eq (by omega), wordCols_eq', show q3Exps[0]! = 4 from rfl, pow4,
        CFSG.KS.SporSch.C11.id_eq]
      simp only [comp_eq]
      exact congrArg unpack11 (Nat.eq_of_beq_eq_true gen0)
    · rw [w_get1, C_eq (by omega), wordCols_eq', show q3Exps[1]! = 2 from rfl, pow2,
        CFSG.KS.SporSch.C11.id_eq]
      simp only [comp_eq]
      exact congrArg unpack11 (Nat.eq_of_beq_eq_true gen1)
  · rw [C_eq hk]
    refine ⟨(unpack11_bounded _).1, (unpack11_bounded _).2, fun hk0 => ?_, fun g hg => ?_⟩
    · have h := allN_spec par k hk
      rw [show Nat.beq k 0 = false from beq_ne (by omega)] at h
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
      have l1 := lt_of_blt h1
      have l2 := lt_of_blt h3
      rw [P_get hk (by omega), P_get hk (by omega), C_eq (by omega), C_eq (by omega), comp_eq]
      exact ⟨l1, l2, (congrArg unpack11 (Nat.eq_of_beq_eq_true h4)).symm⟩
    · have h := allN_spec (allN_spec edge k hk) g hg
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      have l1 := lt_of_blt h1
      rw [E_get hk hg, C_eq l1, C_eq (by omega), comp_eq]
      exact ⟨l1, (congrArg unpack11 (Nat.eq_of_beq_eq_true h2)).symm⟩
  · rw [C_eq (by omega), CFSG.KS.SporSch.C11.id_eq]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true zero)
  · rw [C_eq (by omega), C_eq hk]
    exact ne_sound (allN_spec (allN_spec dist k hk) k' hk')
  · have h := allN_spec fix k hk
    rw [show Nat.beq k 0 = false from beq_ne (by omega)] at h
    rw [C_eq hk]
    exact fixLe_sound h

end CertificateChecks.KernelSporSch.J4Three

end
