module

public import Certificates.Kernel.GMS78.W115Chk
public import CFSG.Certificates.Kernel.GMS78RuWNeSound

public section

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.GMSW CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.VecSurj CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm CFSG.ComponentClassification.GMS78.RuNE
open CertificateChecks.KernelSpor.SmallF2Rels (mat mat_one mat_injective)

local notation "Dt" => CFSG.Sporadic.Ru.Native.ruData

local notation "MUL" => CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28)
  (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM

theorem pair_ne {R : List (List (Nat × Bool))} {n : Nat} (hb : relsBounded R 9 = true)
    (hall : relsNeAll RG MUL R 9 CFSG.KD.OrdRu.ONE 0 n = true) (hn : Nat.beq (lenRels R) n = true)
    {u v : List (Fin 7 × Bool)} (hv : pairRelK (u, v) ∈ R) :
    wordProd (img pi7RuSpec (seedG Dt)) (u.map fun l => (l.1.val, l.2)) ≠
      wordProd (img pi7RuSpec (seedG Dt)) (v.map fun l => (l.1.val, l.2)) := by
  obtain ⟨r, hr, e⟩ := exists_nthRel hv
  rw [Nat.eq_of_beq_eq_true hn] at hr
  have hok := relsNeAll_spec hall r hr
  rw [Nat.zero_add] at hok
  have hne := relNe_sound (hnb := rfl) CFSG.KD.OrdRu.consts roots invs hb hok
  rw [e] at hne
  intro h
  apply hne
  have h1 : wordProd phi (pairRelK (u, v)) = 1 := by
    rw [pairRelK_eq, wordProd_append, wordProd_invWord, wordProd_finLetK, wordProd_finLetK, h,
      mul_inv_cancel]
  have h2 := mat_wordProd le_rfl mat_phi _ (CFSG.KS.Ord.relsBounded_spec hb _ hv)
  rw [h1, mat_one] at h2
  exact h2.symm

theorem pi7bRels_hold : ∀ r ∈ pi7bRels, wordProd (img pi7RuSpec (seedG Dt))
    (r.map fun l => (l.1.val, l.2)) = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc) | rfl
  · exact codes_rel RC_bd RC_all RC_len RC_bind c hc
  · exact codes_rel RA_bd RA_all RA_len RA_bind c hc
  · exact codes_rel RNB_bd RNB_all RNB_len RNB_bind c hc
  · exact codes_rel RN13_bd RN13_all RN13_len RN13_bind c hc
  · exact codes_rel RN23_bd RN23_all RN23_len RN23_bind c hc
  · exact codes_rel RNW_bd RNW_all RNW_len RNW_bind _ (List.mem_singleton.2 rfl)

theorem neBasisEqs_hold : ∀ p ∈ neBasisEqs,
    wordProd (img pi7RuSpec (seedG Dt)) (ruAsmNatWord p.1) =
      wordProd (img pi7RuSpec (seedG Dt)) (ruAsmNatWord p.2) := by
  intro p hp
  by_cases h0 : pairRelK p = []
  · rw [pairRelK_eq, List.append_eq_nil_iff, List.reverse_eq_nil_iff, List.map_eq_nil_iff,
      List.map_eq_nil_iff, List.map_eq_nil_iff] at h0
    rw [ruAsmNatWord, ruAsmNatWord, h0.1, h0.2]
  · have hmem := mem_mkPairsK hp h0
    rw [← relsEqK_eq RNE_bind, pairRelK_eq] at hmem
    exact pair_eq RNE_bd RNE_all RNE_len hmem

theorem neT_ne_one : ∀ i < 64, i ≠ 0 → wordProd (img pi7RuSpec (seedG Dt))
    (ruAsmNatWord (neTWord i)) ≠ 1 := by
  intro i hi hi0
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hp : (neTWord (k + 1), ([] : List (Fin 7 × Bool))) ∈ neTNePairs :=
    List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩
  have hmem : pairRelK (neTWord (k + 1), []) ∈ RNT := by
    rw [relsEqK_eq RNT_bind, mkPairsAllK_eq]
    exact List.mem_map_of_mem hp
  exact pair_ne RNT_bd RNT_all RNT_len hmem

theorem neOrbitX_comm_ne : ∀ t ∈ neOrbitWit, ∃ j : ℕ,
    wordProd (img pi7RuSpec (seedG Dt)) (ruAsmNatWord (neOrbitX t ++ ruE0Words.getD j [])) ≠
      wordProd (img pi7RuSpec (seedG Dt)) (ruAsmNatWord (ruE0Words.getD j [] ++ neOrbitX t)) := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hJ : NJ.length = neOrbitWit.length := rfl
  have hi' : i < (neCommPairs NJ).length := by
    rw [neCommPairs, List.length_zipWith, hJ, Nat.min_self]
    exact hi
  refine ⟨NJ[i]'(hJ ▸ hi), ?_⟩
  have e : (neCommPairs NJ)[i] = (neOrbitX neOrbitWit[i] ++ ruE0Words.getD (NJ[i]'(hJ ▸ hi)) [],
      ruE0Words.getD (NJ[i]'(hJ ▸ hi)) [] ++ neOrbitX neOrbitWit[i]) := by
    simp only [neCommPairs, List.getElem_zipWith]
    rfl
  have hp := List.getElem_mem hi'
  rw [e] at hp
  have hmem := List.mem_map_of_mem (f := pairRelK) hp
  rw [← mkPairsAllK_eq, ← relsEqK_eq RNX_bind] at hmem
  exact pair_ne RNX_bd RNX_all RNX_len hmem

theorem neConjTab_lin : ∀ k < 6, ∀ i < 64, (neConjTab.getD k []).getD i 0 = neConjLin k i :=
  linTab_sound neLin

end CertificateChecks.KernelGMS78.W

end
