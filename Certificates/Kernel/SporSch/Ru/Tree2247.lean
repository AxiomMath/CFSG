module

public import Certificates.Kernel.SporSch.Ru.TreeC0
public import Certificates.Kernel.SporSch.Ru.TreeC1
public import Certificates.Kernel.SporSch.Ru.TreeC2
public import Certificates.Kernel.SporSch.Ru.TreeC3
public import Certificates.Kernel.SporSch.Ru.TreeC4
public import Certificates.Kernel.SporSch.Ru.TreeC5
public import CFSG.Certificates.Kernel.SporSch.RuTreeTextSound
public import CFSG.Sporadic.Schreier.RuDefs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.Schreier.RuEnum
public import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuTree

open CFSG.KC.Misc.HexFlat CFSG.KS.RuTree CFSG.Sporadic.RuSchreier

@[expose] def Chunk (cs : List Char) (K : Nat) (E : Nat → Nat) : Prop :=
  cs.length = 6 * K ∧ (∀ k < cs.length, AH cs[k]!) ∧
    ∀ k < K, CFSG.KS.HexText.numA cs (6 * k) 6 = E k

theorem chunk1 {cs : List Char} {n T a b : Nat} {F : Nat → Nat}
    (hF : CFSG.KC.Misc.HexFlat.hexFlat cs 6 n 24 T F = true)
    (hE : isNilK (dropL a (dropL b cs)) = true) (hab : a + b = 6 * n * T) :
    Chunk cs (n * T) (entK n F) := by
  obtain ⟨h1, h2, h3⟩ := chunk_sound hF hE hab
  exact ⟨by rw [h1, Nat.mul_assoc], h2, h3⟩

theorem chunkR {cs : List Char} {n T a b : Nat} {F : Nat → Nat} (hn : 0 < n)
    (hR : RowsOK cs n F 0 T) (hE : isNilK (dropL a (dropL b cs)) = true)
    (hab : a + b = 6 * n * T) : Chunk cs (n * T) (entK n F) := by
  obtain ⟨h1, h2, h3⟩ := chunk_of_rows hn hR hE hab
  exact ⟨by rw [h1, Nat.mul_assoc], h2, h3⟩

theorem rows1 : RowsOK RuTreeC1.chars 151 RuTreeC1.F 0 883 :=
  rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p0)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p1)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p2)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p3)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p4)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p5)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p6)
    ((rows_of_run (by decide) (by decide) (by decide) RuTreeC1.p7))))))))

theorem rows2 : RowsOK RuTreeC2.chars 151 RuTreeC2.F 0 883 :=
  rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p0)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p1)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p2)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p3)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p4)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p5)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p6)
    ((rows_of_run (by decide) (by decide) (by decide) RuTreeC2.p7))))))))

theorem rows3 : RowsOK RuTreeC3.chars 151 RuTreeC3.F 0 883 :=
  rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p0)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p1)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p2)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p3)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p4)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p5)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p6)
    ((rows_of_run (by decide) (by decide) (by decide) RuTreeC3.p7))))))))

theorem rows4 : RowsOK RuTreeC4.chars 151 RuTreeC4.F 0 883 :=
  rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p0)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p1)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p2)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p3)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p4)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p5)
    (rows_cat (rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p6)
    ((rows_of_run (by decide) (by decide) (by decide) RuTreeC4.p7))))))))

theorem ch0 : Chunk RuTreeC0.chars (91 * 15) (entK 91 RuTreeC0.F) :=
  chunk1 (a := 0) (b := 8190) RuTreeC0.all RuTreeC0.tail rfl
theorem ch1 : Chunk RuTreeC1.chars (151 * 883) (entK 151 RuTreeC1.F) :=
  chunkR (a := 399999) (b := 399999) (by decide) rows1 RuTreeC1.tail rfl
theorem ch2 : Chunk RuTreeC2.chars (151 * 883) (entK 151 RuTreeC2.F) :=
  chunkR (a := 399999) (b := 399999) (by decide) rows2 RuTreeC2.tail rfl
theorem ch3 : Chunk RuTreeC3.chars (151 * 883) (entK 151 RuTreeC3.F) :=
  chunkR (a := 399999) (b := 399999) (by decide) rows3 RuTreeC3.tail rfl
theorem ch4 : Chunk RuTreeC4.chars (151 * 883) (entK 151 RuTreeC4.F) :=
  chunkR (a := 399999) (b := 399999) (by decide) rows4 RuTreeC4.tail rfl
theorem ch5 : Chunk RuTreeC5.chars (16 * 3692 + 5) (entK2 16 3692 RuTreeC5.F RuTreeC5.R.F) :=
  chunk_sound2 (a := 0) (b := 354462) RuTreeC5.all RuTreeC5.R.all RuTreeC5.tail rfl

theorem sz {s : String} {cs : List Char} {m : Nat} (e : s = String.ofList cs) (hl : cs.length = m)
    (h : ∀ k < cs.length, AH cs[k]!) : s.toUTF8.size = m := by
  rw [e, size_ofList (fun k hk => (h k hk).1), hl]

theorem size : ruBytesTree.size = 6 * 593774 := by
  have e : ruBytesTree = ruTreeText0.toUTF8 ++ ruTreeText1.toUTF8 ++ ruTreeText2.toUTF8 ++
      ruTreeText3.toUTF8 ++ ruTreeText4.toUTF8 ++ ruTreeText5.toUTF8 := by
    rw [ruBytesTree, ruTreeText]
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append]
  rw [e]
  simp only [ByteArray.size_append, sz RuTreeC0.eq ch0.1 ch0.2.1, sz RuTreeC1.eq ch1.1 ch1.2.1,
    sz RuTreeC2.eq ch2.1 ch2.2.1, sz RuTreeC3.eq ch3.1 ch3.2.1, sz RuTreeC4.eq ch4.1 ch4.2.1,
    sz RuTreeC5.eq ch5.1 ch5.2.1]

theorem neg : (!isNilK (dropL 0 (dropL 8184 RuTreeC0.chars))) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuTree

end
