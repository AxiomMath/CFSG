module

public import Certificates.Kernel.Sporadic.M12Order12
public import CFSG.Certificates.Kernel.Spor.PCount12Sound

public section

namespace CertificateChecks.KernelSpor.M12Count

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt

theorem split4₁₂ {α : Type*} (l : List α) (hl : l.length ≤ 12) :
    l = l.take 3 ++ ((l.drop 3).take 3 ++ ((l.drop 6).take 3 ++ (l.drop 9).take 3)) := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · intro i h₁ h₂
    simp only [List.getElem_append, List.getElem_take, List.getElem_drop, List.length_take,
      List.length_drop]
    split_ifs <;> congr 1 <;> omega

theorem sum_ordTwelve :
    ((enumeration m12Certificate).map fun h =>
      ordTwelve 12 4 (mask 4) (pk (1 : Equiv.Perm (Fin 12))) (pk h)).sum = 0 := by
  have hn : (12 : Nat) ≤ 16 := by norm_num
  obtain ⟨T0, rest, hlv⟩ : ∃ T0 rest, lv = T0 :: rest := by
    cases h : lv with
    | nil =>
      have := Nat.eq_of_beq_eq_true lens
      rw [h] at this
      simp at this
    | cons T0 rest => exact ⟨T0, rest, rfl⟩
  have hT0 : T0.length ≤ 12 := by
    have := Nat.le_of_ble_eq_true len₀
    rw [hlv] at this
    simpa using this
  have hcnt : ∀ j, cnt12S j = ((products (((T0.drop (3 * j)).take 3) :: rest)).map fun h =>
      ordTwelve 12 4 (mask 4) (pk (1 : Equiv.Perm (Fin 12))) (pk h)).sum := by
    intro j
    have hs : slice j = ((T0.drop (3 * j)).take 3) :: rest := by rw [slice, hlv]; rfl
    rw [cnt12S, I, ← hs, pcnt_pk hn, Nat.zero_add]
    simp only [one_mul]
  have e0 := hcnt 0
  have e1 := hcnt 1
  have e2 := hcnt 2
  have e3 := hcnt 3
  simp only [Nat.reduceMul, List.drop_zero] at e0 e1 e2 e3
  have hL : enumeration m12Certificate = products lv := rfl
  rw [hL, hlv, split4₁₂ T0 hT0, products_append_head, products_append_head, products_append_head]
  simp only [List.map_append, List.sum_append]
  rw [← e0, ← e1, ← e2, ← e3]
  have v0 := Nat.eq_of_beq_eq_true o12s0
  have v1 := Nat.eq_of_beq_eq_true o12s1
  have v2 := Nat.eq_of_beq_eq_true o12s2
  have v3 := Nat.eq_of_beq_eq_true o12s3
  omega

theorem no_order_twelve : (orderTables m12Certificate 12).length = 0 := by
  have hn : (12 : Nat) ≤ 16 := by norm_num
  rw [(forall₂_orderTables (by norm_num) m12Certificate (m := 12) (by norm_num)).length_eq,
    List.length_reverse, ← List.countP_eq_length_filter, ← sum_ite_eq_countP]
  have e : ((enumeration m12Certificate).map fun h => if orderOf h = 12 then 1 else 0) =
      (enumeration m12Certificate).map fun h =>
        ordTwelve 12 4 (mask 4) (pk (1 : Equiv.Perm (Fin 12))) (pk h) :=
    List.map_congr_left fun h _ => (ordTwelve_pk hn h).symm
  rw [e]
  exact sum_ordTwelve

end CertificateChecks.KernelSpor.M12Count

end
