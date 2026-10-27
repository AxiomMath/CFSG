
module

public import Certificates.Kernel.SporSch.Ru.RChain
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSporSch.RuR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem field_get {f j : Nat} (hj : j < (ruLines1920.getD f (0, 0)).2) :
    (ruField1920 f)[j]! = ruArr1920 ((ruLines1920.getD f (0, 0)).1 + j) := by
  rw [ruField1920, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem bindsR : Binds 1920 11 RuRS.S 7 2 RuRS.BP (ruField1920 4) (ruBaseArr 1920 ruRBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [ruField1920, ruLines1920],
    fun j hj => by
      have e : RuRS.S j = RuT1920.L (34 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKR j hj)
      have h1 : (ruLines1920.getD 4 (0, 0)).1 = 34 := rfl
      have h2 : (ruLines1920.getD 4 (0, 0)).2 = 7 := rfl
      rw [field_get (f := 4) (by omega), e]
      exact row1920 (by omega),
    by simp [ruBaseArr, ruRBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKR t ht)⟩

theorem bindsS :
    Binds 1920 11 RuSS1920.S 7 2 RuSS1920.BP (ruField1920 1) (ruBaseArr 1920 ruSBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [ruField1920, ruLines1920],
    fun j hj => by
      have e : RuSS1920.S j = RuT1920.L (7 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKS j hj)
      have h1 : (ruLines1920.getD 1 (0, 0)).1 = 7 := rfl
      have h2 : (ruLines1920.getD 1 (0, 0)).2 = 7 := rfl
      rw [field_get (f := 1) (by omega), e]
      exact row1920 (by omega),
    by simp [ruBaseArr, ruSBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKS t ht)⟩

end CertificateChecks.KernelSporSch.RuR

end
