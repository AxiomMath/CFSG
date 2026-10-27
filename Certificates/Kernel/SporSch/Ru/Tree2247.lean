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

theorem ch0 : Chunk RuTreeC0.chars (91 * 15) (entK 91 RuTreeC0.F) :=
  chunk1 (a := 0) (b := 8190) RuTreeC0.all RuTreeC0.tail rfl
theorem ch1 : Chunk RuTreeC1.chars (151 * 883) (entK 151 RuTreeC1.F) :=
  chunk1 (a := 399999) (b := 399999) RuTreeC1.all RuTreeC1.tail rfl
theorem ch2 : Chunk RuTreeC2.chars (151 * 883) (entK 151 RuTreeC2.F) :=
  chunk1 (a := 399999) (b := 399999) RuTreeC2.all RuTreeC2.tail rfl
theorem ch3 : Chunk RuTreeC3.chars (151 * 883) (entK 151 RuTreeC3.F) :=
  chunk1 (a := 399999) (b := 399999) RuTreeC3.all RuTreeC3.tail rfl
theorem ch4 : Chunk RuTreeC4.chars (151 * 883) (entK 151 RuTreeC4.F) :=
  chunk1 (a := 399999) (b := 399999) RuTreeC4.all RuTreeC4.tail rfl
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
