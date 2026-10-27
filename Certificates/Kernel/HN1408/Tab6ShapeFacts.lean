module

public import Certificates.Kernel.HN1408.Tab6CayChk
public import Certificates.Kernel.HN1408.Tab6CommChk
public import Certificates.Kernel.HN1408.Tab6Codes
public import Certificates.Kernel.HN1408.Spec
public import Certificates.Kernel.HN1408.Tab6CntFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.BfsPin CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model
open CFSG.EvenSporadicStandard.HNRecog.Section3

theorem stab_letters (i : Fin 8) :
    ∀ w ∈ (tab6Row i).stabWords classaz.centGens, lettersOK w = true := by
  intro w hw
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hw
  exact lettersOK_specWord (by decide) s

theorem card_d8_s3 : Nat.card (DihedralGroup 4 × Sym 3) = 48 := by
  rw [Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

theorem card_e2_d8 : Nat.card (Multiplicative (Fin 2 → ZMod 2) × DihedralGroup 4) = 32 := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
    Nat.card_fin, DihedralGroup.nat_card]
  norm_num

theorem card_z2_d10 : Nat.card (Z 2 × DihedralGroup 5) = 20 := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, DihedralGroup.nat_card]

theorem card_z2_d8 : Nat.card (Z 2 × DihedralGroup 4) = 16 := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, DihedralGroup.nat_card]

theorem cay2 : cayleyOK tab6Cap 48 ((tab6Row 2).stabWords classaz.centGens) tab6Img2 = true :=
  cayleyOK_of t6Code2 (stab_letters 2) ch441694_h2 ch441694_r2 rfl (by decide +kernel)
    (by decide +kernel) ch441694_c2

theorem cay4 : cayleyOK tab6Cap 32 ((tab6Row 4).stabWords classaz.centGens) tab6Img4 = true :=
  cayleyOK_of t6Code4 (stab_letters 4) ch441694_h4 ch441694_r4 rfl (by decide +kernel)
    (by decide +kernel) ch441694_c4

theorem cay6 : cayleyOK tab6Cap 20 ((tab6Row 6).stabWords classaz.centGens) tab6Img6 = true :=
  cayleyOK_of t6Code6 (stab_letters 6) ch441694_h6 ch441694_r6 rfl (by decide +kernel)
    (by decide +kernel) ch441694_c6

theorem cay7 : cayleyOK tab6Cap 16 ((tab6Row 7).stabWords classaz.centGens) tab6Img7 = true :=
  cayleyOK_of t6Code7 (stab_letters 7) ch441694_h7 ch441694_r7 rfl (by decide +kernel)
    (by decide +kernel) ch441694_c7

theorem tab6_shape2 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 2).stabWords classaz.centGens}))
    ≃* (DihedralGroup 4 × Sym 3)) := nonempty_mulEquiv_of_cayleyOK cay2 card_d8_s3

theorem tab6_shape4 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 4).stabWords classaz.centGens}))
    ≃* (Elem2 2 × DihedralGroup 4)) := nonempty_mulEquiv_of_cayleyOK cay4 card_e2_d8

theorem tab6_shape6 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 6).stabWords classaz.centGens}))
    ≃* (Z 2 × DihedralGroup 5)) := nonempty_mulEquiv_of_cayleyOK cay6 card_z2_d10

theorem tab6_shape7 : Nonempty (↥(closure (elemW '' {w | w ∈ (tab6Row 7).stabWords classaz.centGens}))
    ≃* (Z 2 × DihedralGroup 4)) := nonempty_mulEquiv_of_cayleyOK cay7 card_z2_d8

theorem comm_of_commP' {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h)
    (hc : commP X Y = true) : g * h = h * g := by
  have h1 := repC_pc hX hY
  rw [Nat.eq_of_beq_eq_true hc] at h1
  exact eq_of_repC h1 (repC_pc hY hX)

theorem gi_eq {ws : List (List Nat)} {m cap cnt : Nat} {G GI GJ TT PL : Nat → Nat}
    (hd : cyHd ws m cap G GI GJ TT PL cnt = true) {j : Nat} (hj : j < ws.length) :
    GI j = WK (ws.getD j []) := by
  unfold cyHd at hd
  obtain ⟨hd1, -⟩ := cyBA hd
  exact Nat.eq_of_beq_eq_true (cyBA (allN_spec hd1 j hj)).1

theorem mem_stab_of {w : List Nat} (hw : lettersOK w = true) {i : Fin 8}
    (hy : commP (WK w) (WK wordAZ) = true)
    (hc : commP (WK w) (WK ((tab6Row i).conj ++ wordAZ ++ (tab6Row i).conj.reverse)) = true) :
    elemW w ∈ P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({(tab6Row i).repElem wordAZ} : Set (Equiv.Perm (Fin 1408))) := by
  refine mem_inf.2 ⟨mem_inf.2 ⟨elemW_mem w, ?_⟩, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    exact comm_of_commP' (repC_word hw) (repC_word (by decide)) hy
  · rw [mem_centralizer_singleton_iff]
    exact comm_of_commP' (repC_word hw) (repC_row (letters_row i).1 (letters_row i).2) hc

theorem sub_of {i : Fin 8} {m cap cnt : Nat} {G GI GJ TT PL : Nat → Nat}
    (hd : cyHd ((tab6Row i).stabWords classaz.centGens) m cap G GI GJ TT PL cnt = true)
    (hk : allN ((tab6Row i).stabWords classaz.centGens).length (fun j =>
      bAnd(commP (GI j) (WK wordAZ),
        commP (GI j) (WK ((tab6Row i).conj ++ wordAZ ++ (tab6Row i).conj.reverse)))) = true) :
    closure (elemW '' {w | w ∈ (tab6Row i).stabWords classaz.centGens}) ≤
      P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({(tab6Row i).repElem wordAZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
  have e : GI j = WK (((tab6Row i).stabWords classaz.centGens).getD j []) := gi_eq hd hj
  rw [List.getD_eq_getElem _ _ hj] at e
  obtain ⟨k1, k2⟩ := cyBA (allN_spec hk j hj)
  rw [e] at k1 k2
  exact mem_stab_of (stab_letters i _ (List.getElem_mem hj)) k1 k2

theorem tab6_sub2 :
    closure (elemW '' {w | w ∈ (tab6Row 2).stabWords classaz.centGens}) ≤
      P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({(tab6Row 2).repElem wordAZ} : Set (Equiv.Perm (Fin 1408))) :=
  sub_of ch441694_h2 ch441694_k2

theorem tab6_sub4 :
    closure (elemW '' {w | w ∈ (tab6Row 4).stabWords classaz.centGens}) ≤
      P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({(tab6Row 4).repElem wordAZ} : Set (Equiv.Perm (Fin 1408))) :=
  sub_of ch441694_h4 ch441694_k4

theorem tab6_sub6 :
    closure (elemW '' {w | w ∈ (tab6Row 6).stabWords classaz.centGens}) ≤
      P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({(tab6Row 6).repElem wordAZ} : Set (Equiv.Perm (Fin 1408))) :=
  sub_of ch441694_h6 ch441694_k6

theorem tab6_sub7 :
    closure (elemW '' {w | w ∈ (tab6Row 7).stabWords classaz.centGens}) ≤
      P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({(tab6Row 7).repElem wordAZ} : Set (Equiv.Perm (Fin 1408))) :=
  sub_of ch441694_h7 ch441694_k7

theorem tab6_mem5A : wordP tab65AWord ∈ Gx (wordP wordAZ) ⊓ Gx ((tab6Row 5).rowP wordAZ) := by
  have h := mem_stab_of (i := 5) (w := tab65AWord) (by decide) ch441694_k5y ch441694_k5c
  obtain ⟨h1, h2⟩ := mem_inf.1 h
  obtain ⟨-, h1⟩ := mem_inf.1 h1
  rw [mem_centralizer_singleton_iff] at h1 h2
  refine mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_Gx]
    exact Subtype.ext h1.symm
  · rw [mem_Gx]
    exact Subtype.ext h2.symm

end CFSG.KD.HN1408.Tab6

end
