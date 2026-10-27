
module

public import CFSG.Sporadic.Schreier.J4SCommGenInputs
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.J4S.XY
public import CFSG.Certificates.Kernel.SporSch.J4STokSound
public import CFSG.Certificates.Kernel.SporSch.J4SSpanSound
meta import CFSG.Sporadic.Schreier.J4SData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.J4SW CFSG.Sporadic.J4Schreier.strongWordsText

#kss_tokens CertificateChecks.KernelSporSch.J4SW CFSG.Sporadic.J4Schreier.strongWordsText

#kss_words CertificateChecks.KernelSporSch.J4SW CFSG.Sporadic.J4Schreier.strongWordsText 9

namespace CertificateChecks.KernelSporSch.J4CommGen

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.Schreier.PairText
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

theorem words_eq : strongWords = J4SW.ws.toArray := by
  rw [strongWords, J4SW.eq, CFSG.KS.SporSch.tokK_sound J4SW.tok]
  exact tokWords_sound J4SW.wtok

@[expose] def V : List Nat := [6, 12, 80, 154, 1280, 583, 1052, 288, 697, 1828, 497]

@[expose] noncomputable def cvK (w : List Int) (j v : Nat) : Bool :=
  Nat.beq (Nat.xor (Nat.pow 2 j) (appK (W w) (Nat.pow 2 j))) v

theorem v0 : cvK J4SW.w1 1 6 = true := by quickRfl
theorem v1 : cvK J4SW.w1 2 12 = true := by quickRfl
theorem v2 : cvK J4SW.w1 4 80 = true := by quickRfl
theorem v3 : cvK J4SW.w1 5 154 = true := by quickRfl
theorem v4 : cvK J4SW.w1 8 1280 = true := by quickRfl
theorem v5 : cvK J4SW.w1 10 583 = true := by quickRfl
theorem v6 : cvK J4SW.w2 1 1052 = true := by quickRfl
theorem v7 : cvK J4SW.w2 2 288 = true := by quickRfl
theorem v8 : cvK J4SW.w2 3 697 = true := by quickRfl
theorem v9 : cvK J4SW.w2 5 1828 = true := by quickRfl
theorem v10 : cvK J4SW.w6 4 497 = true := by quickRfl

theorem span : spanK V = true := by quickRfl

theorem g0 : gens1[0]! = wordCols J4SW.w1 := by
  rw [show gens1[0]! = sCols 1 from rfl, sCols, words_eq]
  rfl

theorem g1 : gens1[1]! = wordCols J4SW.w2 := by
  rw [show gens1[1]! = sCols 2 from rfl, sCols, words_eq]
  rfl

theorem g5 : gens1[5]! = wordCols J4SW.w6 := by
  rw [show gens1[5]! = sCols 6 from rfl, sCols, words_eq]
  rfl

theorem cv {j g v : Nat} {w : List Int} (hg : gens1[g]! = wordCols w) (h : cvK w j v = true) :
    commVec (j, g) = v := by
  rw [commVec, hg, wordCols_eq', app_eq]
  exact Nat.eq_of_beq_eq_true h

theorem vecs_eq : commPicks.map commVec = V := by
  rw [show commPicks.map commVec = [commVec (1, 0), commVec (2, 0), commVec (4, 0),
    commVec (5, 0), commVec (8, 0), commVec (10, 0), commVec (1, 1), commVec (2, 1),
    commVec (3, 1), commVec (5, 1), commVec (4, 5)] from rfl, cv g0 v0, cv g0 v1, cv g0 v2,
    cv g0 v3, cv g0 v4, cv g0 v5, cv g1 v6, cv g1 v7, cv g1 v8, cv g1 v9, cv g5 v10]
  rfl

theorem facts : ∀ c < 2048, ∃ m < 2048, xorSub (commPicks.map commVec) m = c := by
  rw [vecs_eq]
  exact span_sound span

end CertificateChecks.KernelSporSch.J4CommGen

end
