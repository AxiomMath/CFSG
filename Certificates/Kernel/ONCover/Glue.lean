module

public import Certificates.Kernel.CosPres.F291371A
public import Certificates.Kernel.ONCover.SL37
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Certificates.Kernel.Mat3WordSound

public section

namespace CertificateChecks.KernelONCover

open CFSG.CosetTable CFSG.KC.MiscCoset
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

@[expose] def decW (m : ℕ) (w : List (ℕ × Bool)) : List (Fin m × Bool) :=
  w.filterMap fun l => if h : l.1 < m then some (⟨l.1, h⟩, l.2) else none

theorem card_of_perm {m : ℕ} {ws ws' : List (List (Fin m × Bool))} (h : ws.Perm ws') {N : ℕ}
    (hc : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N) :
    Finite (PG m ws') ∧ Nat.card (PG m ws') ≤ N := by
  have e : {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} =
      {r : FreeGroup (Fin m) | r ∈ ws'.map FreeGroup.mk} :=
    Set.ext fun r => (h.map _).mem_iff
  have hc' : Finite (PresentedGroup {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) ∧
      Nat.card (PresentedGroup {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) ≤ N := hc
  rw [e] at hc'
  exact hc'

@[expose] def mainWs₁U : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) (cov ++ rsWs)

theorem mainWs₁_perm : mainWs₁.Perm mainWs₁U := by
  unfold mainWs₁ mainWs₁U mainWs byLength restrictWords
  exact (List.mergeSort_perm _ _).filterMap _

@[expose] def wsB : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  CFSG.KBRoute.F291371b.rels.map (decW _)

theorem wsB_enc : wsB.map encW = CFSG.KBRoute.F291371b.rels := by decide +kernel

theorem wsB_restrict : (restrictWords (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) wsB).map encW =
    CFSG.KBRoute.F291371c.rels := by
  decide +kernel

theorem wsB_perm : wsB.Perm mainWs₁U := by decide +kernel

theorem card_mainWs₁_le :
    Finite (PG _ mainWs₁) ∧ Nat.card (PG _ mainWs₁) ≤ 1876896 := by
  have hb := CFSG.KBFact.F291371b
  rw [← wsB_enc] at hb
  have hc := CFSG.KBFact.F291371c
  rw [← wsB_restrict] at hc
  obtain ⟨f, c⟩ := TableFact.card_restrict wsB (by decide)
    (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) (by decide) hb hc
  exact card_of_perm (wsB_perm.trans mainWs₁_perm.symm) ⟨f, c.trans (by norm_num)⟩

theorem hatS_perm : hatS.Perm hatSU := by
  unfold hatS byLength hatSU
  exact List.mergeSort_perm _ _

@[expose] def wsD : List (List (Fin 4 × Bool)) := CFSG.KBRoute.F291371d.rels.map (decW 4)

theorem wsD_enc : wsD.map encW = CFSG.KBRoute.F291371d.rels := by decide +kernel

theorem wsD_restrict : (restrictWords (subsetOf 4 [0, 1]) wsD).map encW =
    CFSG.KBRoute.F291371e.rels := by
  decide +kernel

theorem wsD_perm : wsD.Perm hatSU := by decide +kernel

theorem card_hatS_le : Finite (PG 4 hatS) ∧ Nat.card (PG 4 hatS) ≤ 5630688 := by
  have hd := CFSG.KBFact.F291371d
  rw [← wsD_enc] at hd
  have he := CFSG.KBFact.F291371e
  rw [← wsD_restrict] at he
  obtain ⟨f, c⟩ := TableFact.card_restrict wsD (by norm_num) (subsetOf 4 [0, 1]) (by decide) hd he
  exact card_of_perm (wsD_perm.trans hatS_perm.symm) ⟨f, c.trans (by norm_num)⟩

theorem hatWords_perm : hatWords.Perm hatWordsU := by
  unfold hatWords hatWordsU
  exact ((hatS_perm.map _).cons _).cons _

theorem hat_periods :
    ∃ (Ω : Type) (ψ : PG 4 hatS →* (Equiv.Perm Ω)ᵐᵒᵖ) (b : Ω), ∀ u ℓ, (u, ℓ) ∈ hatWords → 0 < ℓ →
      Function.minimalPeriod (ψ (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
        (FreeGroup.mk u))).unop b = ℓ := by
  obtain ⟨Ω, ψ, b, h⟩ := CFSG.KC.Mat3.check_presented hat_ok (ws := hatS)
    fun r hr => hatS_perm.mem_iff.1 hr
  exact ⟨Ω, ψ, b, fun u ℓ hu hℓ => h u ℓ (hatWords_perm.mem_iff.1 hu) hℓ⟩

end CertificateChecks.KernelONCover

end
