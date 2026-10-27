module

public import Certificates.Kernel.SporSch.J4S.NCharChecks
public import CFSG.Certificates.Kernel.SporSch.J4SNCharSound

public section

namespace CertificateChecks.KernelSporSch.J4NChar

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Five

theorem hE : ∀ e < 1024, elementColumns[e]! = unpack11 (J4E.T e) := fun _ he => E_eq he

theorem hC : conjTab.size = 4 ∧ ∀ i < 4, conjTab[i]! = unpackW 10 1024 (J4IC.T i) := by
  rw [conjTab, J4IC.eq, CFSG.KS.SporSch.tokK_sound J4IC.tok]
  exact permsK_sound J4InvC.pC

theorem CJ_get {i e : Nat} (hi : i < 4) (he : e < 1024) : (conjTab[i]!)[e]! = ent 10 (J4IC.T i) e := by
  rw [hC.2 i hi, unpackW_get he]

theorem mem4 {c : Nat} (h : c ∈ [0, 118, 448, 502]) : ∃ a < 4, k4 a = c := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨3, by omega, rfl⟩

theorem k4_mem {a : Nat} (ha : a < 4) : k4 a ∈ [0, 118, 448, 502] ∧ k4 a < 1024 := by
  interval_cases a <;> exact ⟨by decide, by decide⟩

theorem xor_lt {a b : Nat} (ha : a < 4) (hb : b < 4) : Nat.xor a b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem facts : (uClasses.length = 25 ∧ uWitness.length = 25 ∧
      (∀ c < 25, classForestOK uClasses[c]! = true ∧ classWitOK uClasses[c]! uWitness[c]! = true) ∧
      ∀ e < 1024, e ≠ 0 → quadSelf e = true → ∃ c < 25, e ∈ (uClasses[c]!).map Prod.fst)
    ∧ (∀ i < 4, ∀ j < 11, (genInvColumns[i]!)[j]! < 2048)
    ∧ (fixCount elementColumns[118]! = 128 ∧
      fixCount elementColumns[448]! = 128 ∧ fixCount elementColumns[502]! = 128 ∧
      comp11 elementColumns[448]! elementColumns[502]! = elementColumns[118]! ∧
      comp11 elementColumns[118]! elementColumns[448]! = elementColumns[502]! ∧
      comp11 elementColumns[118]! elementColumns[118]! = idRows 11 ∧
      comp11 elementColumns[448]! elementColumns[448]! = idRows 11 ∧
      (∀ i < 4, (conjTab[i]!)[118]! = 118) ∧
      (∀ i < 4, (conjTab[i]!)[448]! = 448 ∨ (conjTab[i]!)[448]! = 502) ∧
      (∀ i < 4, (conjTab[i]!)[502]! = 448 ∨ (conjTab[i]!)[502]! = 502) ∧
      (∃ i < 4, (conjTab[i]!)[448]! = 502) ∧
      ((Finset.range 2048).filter fun a =>
        app11 elementColumns[118]! a = a ∧ app11 elementColumns[448]! a = a).card = 32 ∧
      (∀ c ∈ [0, 118, 448, 502], ∀ c' ∈ [0, 118, 448, 502], ∀ v < 2048, quadAt c c' v = true) ∧
      (∀ c ∈ [0, 118, 448, 502], ∀ c' ∈ [0, 118, 448, 502], ∃ d ∈ [0, 118, 448, 502],
        comp11 elementColumns[c]! elementColumns[c']! = elementColumns[d]!) ∧
      (∀ c ∈ [118, 448, 502], comp11 elementColumns[c]! elementColumns[c]! = elementColumns[0]!) ∧
      (∀ i < 4, (conjTab[i]!)[448]! ≠ (conjTab[i]!)[502]!) ∧
      ((Finset.range 2048).filter fun a => app11 elementColumns[118]! a = a).card = 128) := by
  have cjp := fun i (hi : i < 4) => allN_spec cj i hi
  refine ⟨⟨rfl, rfl, fun c hc => ?_, ?_⟩, fun i hi j hj => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec fw c hc)
    exact ⟨forestK_sound hC h1, witK_sound hE h2⟩
  · exact coverK_sound hE cov
  · rw [(bind2_sound J4GI.bind).2 i hi]
    exact (unpack11_bounded _).2 j hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    ⟨0, by omega, ?_⟩, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [hE 118 (by omega)]
    exact fix_sound x1
  · rw [hE 448 (by omega)]
    exact fix_sound x2
  · rw [hE 502 (by omega)]
    exact fix_sound x3
  · rw [hE 448 (by omega), hE 502 (by omega), hE 118 (by omega)]
    exact comp_sound cm1
  · rw [hE 448 (by omega), hE 502 (by omega), hE 118 (by omega)]
    exact comp_sound cm2
  · rw [hE 118 (by omega), CFSG.KS.SporSch.C11.id_eq]
    exact comp_sound cm3
  · rw [hE 448 (by omega), CFSG.KS.SporSch.C11.id_eq]
    exact comp_sound cm4
  · rw [CJ_get hi (by omega)]
    exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (cjp i hi)).1
  · obtain ⟨_, h⟩ := (bAnd_iff _ _).1 (cjp i hi)
    obtain ⟨h, _⟩ := (bAnd_iff _ _).1 h
    rw [CJ_get hi (by omega)]
    cases h1 : Nat.beq (ent 10 (J4IC.T i) 448) 448
    · rw [h1] at h
      exact Or.inr (Nat.eq_of_beq_eq_true h)
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · obtain ⟨_, h⟩ := (bAnd_iff _ _).1 (cjp i hi)
    obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h, _⟩ := (bAnd_iff _ _).1 h
    rw [CJ_get hi (by omega)]
    cases h1 : Nat.beq (ent 10 (J4IC.T i) 502) 448
    · rw [h1] at h
      exact Or.inr (Nat.eq_of_beq_eq_true h)
    · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · rw [CJ_get (by omega) (by omega)]
    exact Nat.eq_of_beq_eq_true ex
  · rw [hE 118 (by omega), hE 448 (by omega)]
    exact fix2_sound f2
  · intro c hc c' hc' v hv
    obtain ⟨a, ha, rfl⟩ := mem4 hc
    obtain ⟨b, hb, rfl⟩ := mem4 hc'
    exact quadK_sound hE (k4_mem ha).2 (k4_mem hb).2
      (allN_spec (allN_spec (allN_spec quad a ha) b hb) v hv)
  · intro c hc c' hc'
    obtain ⟨a, ha, rfl⟩ := mem4 hc
    obtain ⟨b, hb, rfl⟩ := mem4 hc'
    refine ⟨k4 (Nat.xor a b), (k4_mem (xor_lt ha hb)).1, ?_⟩
    rw [hE _ (k4_mem ha).2, hE _ (k4_mem hb).2, hE _ (k4_mem (xor_lt ha hb)).2]
    exact comp_sound (allN_spec (allN_spec prod a ha) b hb)
  · intro c hc
    have hc4 : c ∈ [0, 118, 448, 502] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      omega
    obtain ⟨a, ha, rfl⟩ := mem4 hc4
    have e0 : k4 (Nat.xor a a) = 0 := by
      rw [show Nat.xor a a = 0 from Nat.xor_self a]
      rfl
    rw [hE _ (k4_mem ha).2, ← e0, hE _ (k4_mem (xor_lt ha ha)).2]
    exact comp_sound (allN_spec (allN_spec prod a ha) a ha)
  · obtain ⟨_, h⟩ := (bAnd_iff _ _).1 (cjp i hi)
    obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨_, h⟩ := (bAnd_iff _ _).1 h
    rw [CJ_get hi (by omega), CJ_get hi (by omega)]
    intro e
    rw [e, Nat.beq_refl] at h
    exact Bool.false_ne_true h
  · rw [hE 118 (by omega)]
    exact fix_sound x1

end CertificateChecks.KernelSporSch.J4NChar

end
