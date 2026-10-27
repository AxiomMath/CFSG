module

public import Certificates.Kernel.SmithEK.GlueOImg
public import Certificates.Kernel.SmithEK.PinsO
public import CFSG.LargeExtraspecial.SMod20CollCertBase

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.KC.Misc.O73

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos perpTab uaPts

theorem sw_lt : stabWords.size = 34 ∧ ∀ w ∈ stabWords.toList, w.1 < 693 ∧ w.2 < 693 := by
  refine ⟨by decide +kernel, ?_⟩
  have h : (stabWords.toList.all fun w => decide (w.1 < 693) && decide (w.2 < 693)) = true := by
    decide +kernel
  intro w hw
  have := List.all_eq_true.1 h w hw
  simpa using this

theorem sw_mem {g : Nat} (hg : g < 34) : stabWords[g]! ∈ stabWords.toList := by
  have hs : g < stabWords.size := sw_lt.1 ▸ hg
  rw [getElem!_pos stabWords g hs]
  exact Array.getElem_mem_toList hs

theorem stabAp_TP {w : Nat × Nat} (hw : w ∈ stabWords.toList) {x : Nat} (hx : x < 693) :
    stabAp tvTabs w x = at' 10 (CFSG.KD.Misc.Xi.TP ((w.1 + 1024 * w.2) % 1024))
      (at' 10 (CFSG.KD.Misc.Xi.TP ((w.1 + 1024 * w.2) / 1024)) x) ∧
      stabAp tvTabs w x < 693 := by
  obtain ⟨h1, h2⟩ := sw_lt.2 w hw
  have e1 : (w.1 + 1024 * w.2) % 1024 = w.1 := by omega
  have e2 : (w.1 + 1024 * w.2) / 1024 = w.2 := by omega
  have hb := ap_tvTabs_TP h2 hx
  have ha := ap_tvTabs_TP h1 hb.2
  rw [e1, e2]
  unfold stabAp
  rw [hb.1, ha.1]
  exact ⟨rfl, ha.2⟩

theorem stab_fix {g : Nat} (hg : g < 34) {k : Nat} (hk : k < 21) :
    uaMem uaPts[0]! (stabAp tvTabs stabWords[g]! (uaPts[0]!)[k]!) = true := by
  obtain ⟨-, hlt, -⟩ := CFSG.LargeExtraspecial.SMod20.uaPlane_parts (i := 0) (by omega)
  have hw := sw_mem hg
  have hS := stabAp_TP hw (hlt k hk)
  have hc : stabWords[g]!.1 + 1024 * stabWords[g]!.2 ∈ po.SW := by
    rw [← c21262sw]
    exact List.mem_map_of_mem hw
  have h := stabK_sound c21262stab_0 _ hc _ (uaPts_mem_pl (j := 0) (by omega) hk)
  rw [uaMem_pb (by omega) hS.2, hS.1]
  exact h

theorem co_get (k : Nat) : uaCo[k]! = po.CO.getD k 0 := by
  rw [← c21262co]
  simp only [List.getD_eq_getElem?_getD, getElem!_def, Array.getElem?_toList]
  cases uaCo[k]? <;> rfl

theorem uaCls_eq {v : Nat} (hv : v < 512) : uaCls collS2 v = clsK po.CO (s2K po.CO) v := by
  have hmem : uaMem uaCo v = memK v po.CO := by
    apply Bool.eq_iff_iff.2
    rw [memK_iff, ← c21262co]
    unfold uaMem
    rw [anyIn_eq_true]
    constructor
    · rintro ⟨k, hk, he⟩
      rw [beq_iff_eq] at he
      have hs : k < uaCo.size := by
        have : uaCo.size = 21 := by decide +kernel
        omega
      rw [getElem!_pos uaCo k hs] at he
      rw [← he]
      exact Array.getElem_mem_toList hs
    · intro h
      obtain ⟨k, hk, he⟩ := List.getElem_of_mem h
      have hk' : k < 21 := by
        have : uaCo.toList.length = 21 := by decide +kernel
        omega
      refine ⟨k, hk', ?_⟩
      rw [beq_iff_eq, getElem!_pos uaCo k (by simpa using hk), ← he]
      simp
  have hs2 : collS2[v]! = bitK (s2K po.CO) v := by
    apply Bool.eq_iff_iff.2
    rw [CFSG.LargeExtraspecial.SMod20.collS2_get hv, bitK_eq, s2K_testBit]
    simp only [co_get]
    rfl
  unfold uaCls clsK
  rw [hmem, hs2]
  by_cases h0 : v = 0
  · subst h0
    rfl
  · have : Nat.beq v 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
    simp only [this, cond_false, beq_iff_eq, h0, if_false]
    cases memK v po.CO <;> cases bitK (s2K po.CO) v <;> rfl

theorem cls_facts : (uaCls collS2 1 = 1 ∧ uaCls collS2 3 = 2 ∧ uaCls collS2 19 = 3) ∧
    ((List.range 512).countP (fun v => uaCls collS2 v == 1) = 21 ∧
      (List.range 512).countP (fun v => uaCls collS2 v == 2) = 210 ∧
      (List.range 512).countP (fun v => uaCls collS2 v == 3) = 280) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := clsChkK_sound c21262cls_0
  have hc : ∀ c, (List.range 512).countP (fun v => uaCls collS2 v == c) =
      (List.range 512).countP (fun v => clsK po.CO (s2K po.CO) v == c) := fun c =>
    List.countP_congr fun v hv => by rw [uaCls_eq (List.mem_range.1 hv)]
  rw [hc, hc, hc, uaCls_eq (by omega), uaCls_eq (by omega), uaCls_eq (by omega)]
  exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩

end CertificateChecks.KernelSmithEK
