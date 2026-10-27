
module

public import Certificates.Kernel.HN1408.Tr2Facts
public import Certificates.Kernel.HN1408.Cz1TChk
public import Certificates.Kernel.HN1408.ClsRFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Cz1T

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.Tr2
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem cz1T_ok : Tr2OK classz₁.centGens wordZ₁ 160 24 2 G T0 P0 S SR T1 P1 where
  letters l hl := by
    have hl2 : l < 2 := hl
    interval_cases l <;> decide
  zw := by decide
  head := cz1T_head
  keys := cz1T_keys
  tree := cz1T_tree
  sch := cz1T_sch
  t1 := cz1T_t1

theorem cz1_card_ge : 3840 ≤ Nat.card (genC classz₁.centGens) := card_ge cz1T_ok

theorem cz1_le_cent :
    genC classz₁.centGens ≤ P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) :=
  le_cent cz1T_ok

theorem z1_facts (hP : Nat.card ↥P1408 = 177408000) :
    (conjClass P1408 elemZ₁).ncard = 46200 ∧
      Nat.card ↥(P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) = 3840 ∧
      genC classz₁.centGens = P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) := by
  have hm := ncard_conjClass_mul_card P1408 elemZ₁
  rw [hP] at hm
  have hcl := ClsR.class_z1_ge
  have hle := Subgroup.card_le_of_le cz1_le_cent
  have hge := cz1_card_ge
  have hK : Nat.card ↥(P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) ≤ 3840 := by
    by_contra hlt
    have h1 : 46200 * 3841 ≤ (conjClass P1408 elemZ₁).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul hcl (by omega)
    omega
  have hc : (conjClass P1408 elemZ₁).ncard ≤ 46200 := by
    by_contra hlt
    have h1 : 46201 * 3840 ≤ (conjClass P1408 elemZ₁).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  exact ⟨by omega, by omega, Subgroup.eq_of_le_of_card_ge cz1_le_cent (by omega)⟩

end CFSG.KD.HN1408.Cz1T

end
