module

public import Certificates.Kernel.Sporadic.He.Bind2112
public import Certificates.Kernel.Sporadic.He.Canon2112
public import Certificates.Kernel.Sporadic.He.RelA2112
public import Certificates.Kernel.Sporadic.He.RelB2112
public import Certificates.Kernel.Sporadic.He.RelC2112
public import Certificates.Kernel.Sporadic.He.RelD2112
public import CFSG.Sporadic.Bridge.HeSurj
public import Certificates.Certificate9118
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He2112

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

theorem relsOK : ∀ v ∈ CFSG.KD.OrdHe.rels, Nat.beq (wordPK 8330 14 G GI v) (pidn 8330 14) = true := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
  have hk7 : k < 7 := by simpa [CFSG.KD.OrdHe.rels] using hk
  rw [← List.getD_eq_getElem _ [] hk]
  interval_cases k
  exacts [rel0, rel1, rel2, rel3, rel4, rel5, rel6]

@[expose] noncomputable def g (k : Nat) : Equiv.Perm (Fin 8330) := permOfArr 8330 (unpack 8330 14 (HeC.S k))

theorem rep_g (k : Nat) (hk : k < 9) : Rep 8330 (unpack 8330 14 (HeC.S k)) (g k) ∧
    Rep 8330 (unpack 8330 14 (HeC.SI k)) (g k)⁻¹ :=
  rep_permOfArr (invEqK_sound (allN_spec perm k hk)).2

theorem relators : ∀ v ∈ Sporadic.hePresentation.relatorLetters, wordProd (img2 (g 0) (g 1)) v = 1 := by
  rw [CFSG.KD.OrdHe.rels_eq]
  have hi : ∀ i, img2 (g 0) (g 1) i = g (if i = 0 then 0 else 1) := by
    intro i
    unfold img2
    split <;> rfl
  have hGi : ∀ i, G i = HeC.S (if i = 0 then 0 else 1) ∧ GI i = HeC.SI (if i = 0 then 0 else 1) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact ⟨rfl, rfl⟩
    · have hb : Nat.beq i 0 = false := by cases i with | zero => omega | succ k => rfl
      unfold G GI
      rw [hb, ite_eq_right_iff.2 (fun h => absurd h (by omega))]
      exact ⟨rfl, rfl⟩
  have hid := (bAnd_iff (canonK 8330 14 (mask 14) (8330 * 14) (pidn 8330 14))
    (idK 8330 14 (mask 14))).1 idOK
  refine relators_of_wordPK (G := G) (GI := GI) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    hid.1 (idK_sound hid.2).symm relsOK
  · rw [hi, (hGi i).1]
    exact (rep_g _ (by split <;> omega)).1
  · rw [hi, (hGi i).2]
    exact (rep_g _ (by split <;> omega)).2
  · rw [(hGi i).1, (hGi i).2]
    exact (bAnd_iff _ _).1 (allN_spec canonOK _ (by split <;> omega))

theorem orbits : rawOrbitSizes 8330 heStrongArrs heBase.toArray = [8330, 4480, 3, 18, 2] := by
  rw [rawOrbitSizesK_orb binds perm HeC.ho (by norm_num)]
  decide

theorem range_two (f : Nat → Equiv.Perm (Fin 8330)) :
    (Set.range fun j : Fin 2 => f j.val) = {f 0, f 1} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
    Fin.val_zero, Fin.val_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem card_le :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 8330 heStrongArrs[j.val]!)) ≤ (rawOrbitSizes 8330 heStrongArrs heBase.toArray).prod := by
  have e : SporadicName.He.presentation = Sporadic.hePresentation := rfl
  have hfin : Finite SporadicName.He.presentation.Group := Certificates.certificate9118.1
  have hcard : Nat.card SporadicName.He.presentation.Group ≤ 4030387200 :=
    Certificates.certificate9118.2
  rw [e] at hfin hcard
  rw [range_two (fun j => permOfArr 8330 heStrongArrs[j]!), strong_eq 0 (by norm_num),
    strong_eq 1 (by norm_num), orbits]
  exact (card_closure_le Sporadic.hePresentation CFSG.Sporadic.Bridge.He.generatorCount_eq relators).trans
    (hcard.trans (by norm_num))

theorem facts :
    rawChainOK 8330 heGenArrs heStrongArrs heBase.toArray heWords 4 = true ∧
    rawOrbitSizes 8330 heStrongArrs heBase.toArray = [8330, 4480, 3, 18, 2] ∧
    isInvA 8330 heGenArrs[0]! (invCand 8330 heGenArrs[0]!) = true ∧
    isInvA 8330 heGenArrs[1]! (invCand 8330 heGenArrs[1]!) = true := by
  have i0 := invEqK_sound (allN_spec perm 0 (by norm_num))
  have i1 := invEqK_sound (allN_spec perm 1 (by norm_num))
  refine ⟨?_, orbits, ?_, ?_⟩
  · rw [gens_eq, words_eq]
    exact rawChainK_of_card_orb 4 binds HeC.head HeC.ho (by norm_num) card_le
  · rw [gen_eq 0 (by norm_num), i0.1]
    exact i0.2
  · rw [gen_eq 1 (by norm_num), i1.1]
    exact i1.2

end CertificateChecks.KernelSpor.He2112

end
