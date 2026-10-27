module

public import Certificates.Kernel.SmithD6StabTree.Checks
public import Certificates.Kernel.SmithD6Nc.Glue
public import CFSG.Certificates.Kernel.SmithD6StabTreeSound
import all Certificates.Data.SmithD6Model
import all Certificates.Data.SmithD6Stab

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6StabTree

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab
  CFSG.KD.SmithD6Nc CFSG.KD.SmithD6ST CertificateChecks.SmithD6Stab CertificateChecks.SmithD6Nc
  CertificateChecks.SmithD6Trees

theorem st_recs : ∀ i < 365211,
    stRecGo J.lineKeysC.flatten[i]! (pkGet JST.stD 4 i) (pkGet JST.stG 6 i) = true := by
  intro i hi
  have hl : J.lineKeysC.length = 179 := by rw [← lenC_eq, lineKeysC_lenC]
  have hc : i / 2048 < J.lineKeysC.length := by rw [hl]; omega
  have hc179 : i / 2048 < 179 := by rw [hl] at hc; exact hc
  obtain ⟨hf, hlen, -⟩ := chunkOK_sound hc (lineChunks_ok (i / 2048) hc179)
  have hj : i % 2048 < J.lineKeysC[i / 2048].length := by
    rw [hl] at hlen
    split_ifs at hlen with h <;> omega
  have h := stTreeChunks_ok (i / 2048) hc179
  rw [stTreeOK, nthC_eq] at h
  have h2 := stTreeGo_sound _ _ h (i % 2048) (by rw [getD_eq hc]; exact hj)
  have hfi := hf (i % 2048) hj
  have hi' : 2048 * (i / 2048) + i % 2048 = i := Nat.div_add_mod i 2048
  rw [hi'] at hfi
  obtain ⟨hv, hx⟩ := lineKeys_facts.2.2.2 _ _ hfi
  have key : J.lineKeysC.flatten[i]! = (J.lineKeysC.getD (i / 2048) []).getD (i % 2048) 0 := by
    rw [getElem!_pos _ i hv, hx, getD_eq hc]
    exact (getD_eq hj).symm
  rw [Nat.mul_eq, hi'] at h2
  rw [key]
  exact h2

theorem clsK_lt (k : Nat) : clsK k < 6 := by
  unfold clsK clsP
  split_ifs <;> omega

theorem memB_of_find {x v : Nat} (h : KT.find x lineTree = v + 1) : lineTree.memB x = true := by
  unfold KT.memB
  rw [h, Nat.blt_eq]
  omega

theorem posK_of_find {x v : Nat} (h : KT.find x lineTree = v + 1) : posK x = v := by
  unfold posK
  rw [h]
  rfl

def stabStep (u v : Nat) : Prop := ∃ g < stabGens.size, tvImg stabGens[g]! u = v

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
include hK hL

theorem stabKeys_facts : ∀ k ∈ stabKeys,
    lineTree.memB k = true ∧ imgOK k 4098 = true ∧ imgKey k 4098 = 4098 := by
  intro k hk
  obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk1
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hk2
  exact ⟨(lineIdx3_eq hK hL (nc_facts.1 p hp).1).2, (nc_facts.1 p hp).2, hk2.2⟩

theorem stabGens_get {g : Nat} (hg : g < 42) : stabGens.size = 42 ∧
    stabGens[g]! = posK (stKeysL.getD g 0) ∧ stKeysL.getD g 0 ∈ stabKeys := by
  have hlen := nc_facts.2.1
  have hs : (stabKeys.map posK).toArray.size = stabKeys.length := by
    simp only [List.size_toArray, List.length_map]
  have hgl : g < stabKeys.length := by omega
  refine ⟨by rw [stabGens_eq hK hL, hs, hlen], ?_, ?_⟩
  · rw [stabGens_eq hK hL, getElem!_pos _ g (by rw [hs]; exact hgl), stKeysL_eq, getD_eq hgl]
    simp only [List.getElem_toArray, List.getElem_map]
  · rw [stKeysL_eq, getD_eq hgl]
    exact List.getElem_mem hgl

theorem stabGens_facts_of_pinned :
    ∀ g < stabGens.size, stabGens[g]! < 365211 ∧ tvImg stabGens[g]! 0 = 0 := by
  intro g hg
  have h42 : g < 42 := by
    have := (stabGens_get hK hL (g := 0) (by decide)).1
    omega
  obtain ⟨-, hgk, hmem⟩ := stabGens_get hK hL h42
  obtain ⟨hm, hok, himg⟩ := stabKeys_facts hK hL _ hmem
  obtain ⟨hb0, hbm⟩ := posK_base
  refine ⟨by rw [hgk]; exact (key_of_memB hm).1, ?_⟩
  have ht := (tvImg_eq hK hL hm hbm hok).1
  rw [himg, hb0] at ht
  rw [hgk]
  exact ht

theorem stabReach_of_pinned :
    ∀ v < 365211, Relation.ReflTransGen stabStep (stabRep (stabCls v)) v := by
  suffices H : ∀ n, ∀ v < 365211, pkGet JST.stD 4 v ≤ n →
      Relation.ReflTransGen stabStep (stabRep (stabCls v)) v from
    fun v hv => H _ v hv le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv hd
    have := (stRecGo_sound (st_recs v hv)).1
    omega
  | succ n ih =>
    intro v hv hd
    obtain ⟨-, hroot, hstep⟩ := stRecGo_sound (st_recs v hv)
    obtain ⟨-, hn, hfk, -⟩ := lineKeys_facts
    have hv' : v < J.lineKeysC.flatten.length := hn ▸ hv
    have hkf : KT.find J.lineKeysC.flatten[v]! lineTree = v + 1 := by
      rw [getElem!_pos _ v hv']
      exact hfk v hv'
    rw [stabCls_eq hK hv]
    by_cases h1 : pkGet JST.stD 4 v = 1
    · have hk := hroot h1
      have hc := clsK_lt J.lineKeysC.flatten[v]!
      obtain ⟨hlt, hkey, -, -⟩ := rep_facts hK hc
      have hvr : v = repPos.getD (clsK J.lineKeysC.flatten[v]!) 0 :=
        key_inj hv hlt (hk.trans hkey.symm)
      rw [stabRep_eq hK hc, ← hvr]
    · obtain ⟨hg, p, hf, -, hdp, hi, hcl⟩ := hstep h1
      obtain ⟨hp, hpq⟩ := key_of_find hf
      have ihp := ih p hp (by omega)
      rw [stabCls_eq hK hp, hpq, hcl] at ihp
      obtain ⟨hsz, hgk, hmem⟩ := stabGens_get hK hL hg
      have hsm := (stabKeys_facts hK hL _ hmem).1
      obtain ⟨hok, himg⟩ := imgEqN_sound hi (memB_of_find hkf)
      have ht := (tvImg_eq hK hL hsm (memB_of_find hf) hok).1
      rw [posK_of_find hf, himg, posK_of_find hkf] at ht
      refine Relation.ReflTransGen.tail ihp ⟨pkGet JST.stG 6 v, by rw [hsz]; exact hg, ?_⟩
      rw [hgk]
      exact ht

end Model

end CertificateChecks.SmithD6StabTree

end
