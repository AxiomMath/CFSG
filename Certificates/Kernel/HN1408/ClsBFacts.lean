
module

public import Certificates.Kernel.HN1408.TableIShape
public import Certificates.Kernel.HN1408.InvWordChk
public import Certificates.Kernel.HN1408.GensCommChk
public import Certificates.Kernel.HN1408.ClsRFacts
public import Certificates.Kernel.HN1408.Tr2Facts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.ClsR

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin CFSG.KC.Blk
open CFSG.KD.HN1408.Tr2 (genC gen_mem)

theorem gens_le_cent {ws : List (List Nat)} {Zw : List Nat} (hlen : ws.length = 2)
    (hl : ∀ l < 2, lettersOK (ws.getD l []) = true) (hz : lettersOK Zw = true)
    (h : CzInv.gensCommK ws Zw = true) :
    genC ws ≤ P1408 ⊓ centralizer ({elemW Zw} : Set (Equiv.Perm (Fin 1408))) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨elemW_mem w, ?_⟩
  obtain ⟨l, hl2, rfl⟩ : ∃ l < 2, ws.getD l [] = w := by
    have hw' : w ∈ ws := hw
    obtain ⟨l, hl', e⟩ := List.getElem_of_mem hw'
    exact ⟨l, by omega, by rw [List.getD_eq_getElem _ _ hl', e]⟩
  change elemW (ws.getD l []) ∈ centralizer ({elemW Zw} : Set (Equiv.Perm (Fin 1408)))
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  unfold CzInv.gensCommK at h
  rw [strictB_app] at h
  have hc := Nat.eq_of_beq_eq_true (allN_spec h l hl2)
  have hZ : RepC (WK Zw) (elemW Zw) := repC_word hz
  have hG : RepC (WK (ws.getD l [])) (elemW (ws.getD l [])) := repC_word (hl l hl2)
  have h1 := repC_pc hG hZ
  have h2 := repC_pc hZ hG
  rw [hc] at h1
  exact eq_of_repC h2 h1

theorem cb_le_cent :
    genC classb.centGens ≤ P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) :=
  gens_le_cent rfl (fun l hl => by interval_cases l <;> decide) (by decide) CzInv.cbComm_ok

theorem wordG_mem {G0 G1 : Nat} {g0 g1 : Equiv.Perm (Fin 1408)}
    {H : Subgroup (Equiv.Perm (Fin 1408))} (h0 : RepC G0 g0) (h1 : RepC G1 g1) (m0 : g0 ∈ H)
    (m1 : g1 ∈ H) : ∀ (w : List Nat) (acc : Nat) (g : Equiv.Perm (Fin 1408)), RepC acc g → g ∈ H →
      ∃ x ∈ H, RepC (wfoldK 1408 11 (mask 11) (fun l => nIf(Nat.beq l 0, G0, G1)) w acc) x
  | [], _, g, hr, hm => ⟨g, hm, hr⟩
  | l :: w, acc, g, hr, hm => by
    rw [wfoldK_cons]
    have hS : ∃ s ∈ H, RepC (nIf(Nat.beq l 0, G0, G1)) s := by
      cases Nat.beq l 0
      · exact ⟨g1, m1, h1⟩
      · exact ⟨g0, m0, h0⟩
    obtain ⟨s, hs, hsR⟩ := hS
    exact wordG_mem h0 h1 m0 m1 w _ (g * s) (repC_pc hr hsR) (mul_mem hm hs)

theorem wordsIn_mem {gs hs : List (List Nat)} {w0 w1 : List Nat} (hgl : 2 ≤ gs.length)
    (hg : ∀ l < 2, lettersOK (gs.getD l []) = true) (hh : ∀ l < 2, lettersOK (hs.getD l []) = true)
    (h : CzInv.wordsInK gs hs w0 w1 = true) : ∀ l < 2, elemW (hs.getD l []) ∈ genC gs := by
  unfold CzInv.wordsInK at h
  simp only [strictB_app] at h
  obtain ⟨h0, h1⟩ := mkA h
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  unfold CzInv.wordG at e0 e1
  have hG0 := repC_word (hg 0 (by norm_num))
  have hG1 := repC_word (hg 1 (by norm_num))
  have m0 : elemW (gs.getD 0 []) ∈ genC gs := gen_mem (by omega)
  have m1 : elemW (gs.getD 1 []) ∈ genC gs := gen_mem (by omega)
  obtain ⟨x, hx, hxR⟩ := wordG_mem hG0 hG1 m0 m1 w0 idK 1 Tr2.repC_idK (one_mem _)
  obtain ⟨y, hy, hyR⟩ := wordG_mem hG0 hG1 m0 m1 w1 idK 1 Tr2.repC_idK (one_mem _)
  rw [e0] at hxR
  rw [e1] at hyR
  intro l hl
  interval_cases l
  · rw [eq_of_repC (repC_word (hh 0 (by norm_num))) hxR]
    exact hx
  · rw [eq_of_repC (repC_word (hh 1 (by norm_num))) hyR]
    exact hy

theorem ab_mem_cb : elemA ∈ genC classb.centGens ∧ elemB ∈ genC classb.centGens := by
  have h := wordsIn_mem (gs := classb.centGens) (hs := [wordA, wordB]) (by decide)
    (fun l hl => by interval_cases l <;> decide) (fun l hl => by interval_cases l <;> decide)
    CzInv.bWords_ok
  have e0 : [wordA, wordB].getD 0 [] = wordA := rfl
  have e1 : [wordA, wordB].getD 1 [] = wordB := rfl
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  rw [e0] at h0
  rw [e1] at h1
  exact ⟨h0, h1⟩

theorem cb_card_ge : 80640 ≤ Nat.card (genC classb.centGens) := by
  obtain ⟨-, ht3, ht5, -, -, -⟩ := t2_parts
  obtain ⟨hoA, hoB, hcA, hbA, hbB⟩ := basic_ab
  obtain ⟨φ, -, hrange, hker⟩ := blkData_spec dat2
  have ha2 : elemA * elemA = 1 := mul_self_eq_one_of_orderOf_eq_two hoA
  have hb2 : elemB * elemB = 1 := mul_self_eq_one_of_orderOf_eq_two hoB
  have hab : elemA * elemB = elemB * elemA := hcA _ elemB_mem
  have hA1 : elemA ≠ 1 := fun h => by rw [h, orderOf_one] at hoA; cases hoA
  have hB1 : elemB ≠ 1 := fun h => by rw [h, orderOf_one] at hoB; cases hoB
  have hAB : elemA ≠ elemB := fun h => hbB (h ▸ hbA)
  have hVX : closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))) ≤
      closure (elemW '' {w | w ∈ blkData2.gens}) := by
    rw [closure_le]
    rintro _ (rfl | hv)
    · exact ab_mem_cb.1
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact ab_mem_cb.2
  have hfixV : ∀ t ∈ ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))),
      ∀ p : Fin 1408, blkF blkData2.k blkData2.blk (t p) = blkF blkData2.k blkData2.blk p := by
    have eA : blkTrivOK blkData2.blk (tabW wordA) = true := by
      rw [blk2, (tabW_eq (wd := wordA) (by decide)).1,
        blkTrivOK_eq (tabW_eq (wd := wordA) (by decide)).2]
      exact ht3
    have eB : blkTrivOK blkData2.blk (tabW wordB) = true := by
      rw [blk2, (tabW_eq (wd := wordB) (by decide)).1,
        blkTrivOK_eq (tabW_eq (wd := wordB) (by decide)).2]
      exact ht5
    rintro t (rfl | ht)
    · exact fun p => blkTrivOK_spec rA eA p
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact fun p => blkTrivOK_spec rB eB p
  have hVker : ∀ (v : Equiv.Perm (Fin 1408))
      (h : v ∈ closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))), φ ⟨v, hVX h⟩ = 1 :=
    fun v h => (hker ⟨v, hVX h⟩).2 (blkTriv_closure_set hfixV v h)
  have hVcard : Nat.card ↥(closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))) = 4 :=
    TwoHSData.card_closure_pair ha2 hb2 hab hA1 hB1 hAB
  have hrange' : Nat.card ↥φ.range = 20160 := by
    rw [hrange]
    exact blkImage_spec dat2 (by decide) img2
  have hV' : Nat.card ↥((closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))).subgroupOf
      (closure (elemW '' {w | w ∈ blkData2.gens}))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv, hVcard]
  have hle : (closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))).subgroupOf
      (closure (elemW '' {w | w ∈ blkData2.gens})) ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact hVker x (Subgroup.mem_subgroupOf.1 hx)
  have hK : 4 ≤ Nat.card ↥φ.ker := by
    rw [← hV']
    exact Subgroup.card_le_of_le hle
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hrange'] at h
  change 80640 ≤ Nat.card ↥(closure (elemW '' {w | w ∈ blkData2.gens}))
  omega

theorem b_facts (hP : Nat.card ↥P1408 = 177408000) :
    (conjClass P1408 elemB).ncard = 2200 ∧
      Nat.card ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) = 80640 ∧
      genC classb.centGens = P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) := by
  have hm := ncard_conjClass_mul_card P1408 elemB
  rw [hP] at hm
  have hcl := class_b_ge
  have hle := Subgroup.card_le_of_le cb_le_cent
  have hge := cb_card_ge
  have hK : Nat.card ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) ≤ 80640 := by
    by_contra hlt
    have h1 : 2200 * 80641 ≤ (conjClass P1408 elemB).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul hcl (by omega)
    omega
  have hc : (conjClass P1408 elemB).ncard ≤ 2200 := by
    by_contra hlt
    have h1 : 2201 * 80640 ≤ (conjClass P1408 elemB).ncard *
        Nat.card ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  exact ⟨by omega, by omega, Subgroup.eq_of_le_of_card_ge cb_le_cent (by omega)⟩

end CFSG.KD.HN1408.ClsR

end
