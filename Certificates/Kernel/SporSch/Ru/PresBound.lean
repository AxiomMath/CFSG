module

public import Certificates.Kernel.SporSch.Ru.Pres
public import CFSG.Certificates.Kernel.SporSch.RuPresSound
public import CFSG.Certificates.Kernel.Spor.PresCardK
public import CFSG.Sporadic.Bridge.RuSurj
public import Certificates.Certificate9129
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PresCard

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuPres

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.SurjD.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuPD

theorem ws_relK : allN 12 (fun r => wordEqL (wAt WS r) (wAt (ruRels ()) r)) = true := by quickRfl

theorem ws_rel : ∀ r < 12, wAt WS r = (ruRels ()).getD r [] := fun r hr => by
  rw [wordEqL_sound (allN_spec ws_relK r hr), wAt_eq]

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa [Nat.blt_eq] using h

theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (Nat.lt_of_lt_of_le (by simpa [Nat.blt_eq] using e) h) (Nat.lt_irrefl a)

theorem permId : invEqK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (pidn 4060 12) = true := by
  quickRfl

theorem hidA : idA 4060 = unpack 4060 12 (pidn 4060 12) := (idK_sound idOK).symm

@[expose] noncomputable def gx (i : Nat) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 (unpack 4060 12 (Ug i))

theorem gx_ge {i : Nat} (h : 3 ≤ i) : gx i = 1 := by
  have eU : Ug i = pidn 4060 12 := by rw [Ug, blt_false h]
  have hinv := (invEqK_sound permId).2
  rw [← hidA] at hinv
  rw [gx, eU, ← hidA]
  exact (rep_permOfArr hinv).1.unique rep_idA

theorem gen_facts (i : Nat) : Rep 4060 (unpack 4060 12 (Ug i)) (gx i) ∧
    Rep 4060 (unpack 4060 12 (UIg i)) (gx i)⁻¹ ∧
    canonK 4060 12 (mask 12) (4060 * 12) (Ug i) = true ∧
    canonK 4060 12 (mask 12) (4060 * 12) (UIg i) = true := by
  rcases Nat.lt_or_ge i 3 with h | h
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec gensOK i h)
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    have eU : Ug i = U i := by rw [Ug, blt_true h]
    have eUI : UIg i = UI i := by rw [UIg, blt_true h]
    obtain ⟨_, hinv⟩ := invEqK_sound h1
    have hp := rep_permOfArr hinv
    refine ⟨?_, ?_, by rw [eU]; exact h3, by rw [eUI]; exact h4⟩
    · rw [gx, eU]
      exact hp.1
    · rw [gx, eU, eUI]
      exact hp.2
  · have eU : Ug i = pidn 4060 12 := by rw [Ug, blt_false h]
    have eUI : UIg i = pidn 4060 12 := by rw [UIg, blt_false h]
    refine ⟨?_, ?_, by rw [eU]; exact idCanon, by rw [eUI]; exact idCanon⟩
    · rw [eU, ← hidA, gx_ge h]
      exact rep_idA
    · rw [eUI, ← hidA, gx_ge h, inv_one]
      exact rep_idA

theorem word_rep {r : Nat} (hr : r < 14) :
    Rep 4060 (unpack 4060 12 (TT (16 * r))) (wordProd gx (wAt WS r)) := by
  obtain ⟨hk, he⟩ := (bAnd_iff _ _).1 (EC.all r (by change r < 14; exact hr))
  have hlen : (wAt WS r).length ≤ 20 * KK r := by
    rw [← lenL_eq]
    change lenL (wAt WS r) ≤ 20 * ((lenL (wAt WS r) + 19) / 20)
    omega
  have hK : KK r ≤ 10 := Nat.le_of_ble_eq_true hk
  refine (word_chain (fun i => (gen_facts i).1) (fun i => (gen_facts i).2.1)
    (fun i => ⟨(gen_facts i).2.2.1, (gen_facts i).2.2.2⟩) idCanon hidA
    (T := fun q => TT (16 * r + q)) hlen (Nat.eq_of_beq_eq_true he) fun q hq => ?_).1
  have h := JC.all (10 * r + q) (by change 10 * r + q < 140; omega)
  unfold jobF at h
  rw [strictB_eq', strictB_eq'] at h
  have e1 : Nat.div (10 * r + q) 10 = r := by
    change (10 * r + q) / 10 = r
    omega
  have e2 : Nat.mod (10 * r + q) 10 = q := by
    change (10 * r + q) % 10 = q
    omega
  rw [e1, e2, blt_true hq] at h
  rw [← takeL_eq, ← dropL_eq]
  exact Nat.eq_of_beq_eq_true h

theorem relators : ∀ v ∈ TauCeti.SporadicName.Ru.presentation.relatorLetters,
    wordProd gx v = 1 := by
  intro v hv
  have hv' : v ∈ ruRels () := by
    have e := CFSG.Sporadic.Bridge.Ru.relatorLetters_eq
    change v ∈ TauCeti.Sporadic.ruPresentation.relatorLetters at hv
    rw [e] at hv
    exact hv
  obtain ⟨r, hr, hrv⟩ := List.getElem_of_mem hv'
  have hlen : (ruRels ()).length = 12 := rfl
  have hr12 : r < 12 := hlen ▸ hr
  have hw : wAt WS r = v := by
    rw [ws_rel r hr12, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
      Option.getD_some, hrv]
  have h := word_rep (r := r) (by omega)
  have e : TT (16 * r) = pidn 4060 12 := Nat.eq_of_beq_eq_true (allN_spec tgtRel r hr12)
  rw [hw, e, ← hidA] at h
  exact h.unique rep_idA

theorem gx_mem (i : Nat) : gx i ∈ Subgroup.closure (Set.range fun i : Fin 3 => gx i.val) := by
  rcases Nat.lt_or_ge i 3 with h | h
  · exact Subgroup.subset_closure ⟨⟨i, h⟩, rfl⟩
  · rw [gx_ge h]
    exact Subgroup.one_mem _

theorem a_eq {r : Nat} (hr : r < 14) {L : Nat} (hL : L < 45) (hT : TT (16 * r) = RuT4060.L L) :
    permOfArr 4060 (ruArr4060 L) = wordProd gx (wAt WS r) := by
  have h := word_rep hr
  rw [hT, ← RuLines.row4060 hL] at h
  have hinv := RuLines.isInv.1 L hL
  exact (rep_permOfArr hinv).1.unique h

theorem card_ruP_le : Nat.card ruP ≤ 145926144000 := by
  have h0 : ruA0 = wordProd gx (wAt WS 12) := a_eq (by omega) (L := 0) (by omega)
    (Nat.eq_of_beq_eq_true tgtA0)
  have h1 : ruA1 = wordProd gx (wAt WS 13) := a_eq (by omega) (L := 1) (by omega)
    (Nat.eq_of_beq_eq_true tgtA1)
  have hK : ruP ≤ Subgroup.closure (Set.range fun i : Fin 3 => gx i.val) := by
    rw [ruP, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [h0]
      exact wordProd_mem gx_mem _
    · rw [h1]
      exact wordProd_mem gx_mem _
  obtain ⟨hfin, hcard⟩ := (Certificates.certificate9129)
  have hgc : TauCeti.SporadicName.Ru.presentation.generatorCount = 3 :=
    CFSG.Sporadic.Bridge.Ru.generatorCount_eq
  have hfin' : Finite TauCeti.SporadicName.Ru.presentation.Group := hfin
  exact (Subgroup.card_le_of_le hK).trans
    ((CFSG.KS.Pres.card_closure_le_k' _ hgc relators).trans hcard)

end CertificateChecks.KernelSporSch.RuPres

end
