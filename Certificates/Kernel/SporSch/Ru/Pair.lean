module

public import Certificates.Kernel.SporSch.Ru.PairK
public import Certificates.Kernel.SporSch.Ru.Wit
public import CFSG.Certificates.Kernel.SporSch.RuPairSound
public import CFSG.Sporadic.Schreier.RuTreeElt
import Certificates.Kernel.SporSch.Ru.I2250F
import CFSG.Sporadic.Schreier.RuWitReps

public section

namespace CertificateChecks.KernelSporSch.RuPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuBase CFSG.KC.Misc.RuPair
  CFSG.Sporadic.Th.Native CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.EvenSporadicStandard.TwoRu.HypOne CFSG.EvenSporadicStandard.RuStd CFSG.KS.Ru2250
  CertificateChecks.KernelSporSch

theorem tr_unpack (P : Nat) : TR 4060 (tblOfArr (unpack 4060 12 P)) (apP P) := by
  have h := tr_tblOfArr (n := 4060) (a := unpack 4060 12 P) (by simp [unpack])
    (fun x hx => by
      rw [Orb.unpack_get hx]
      exact Nat.lt_trans (CFSG.KS.PackFld.pg_lt 12 _ _) (by decide))
  refine ⟨h.1, fun x hx => ?_⟩
  rw [h.2 x hx]
  exact Orb.unpack_get hx

theorem bij_of_pk {P Q : Nat} (h : RuG.pk P Q = true) : Bij 4060 (apP P) (apP Q) := by
  obtain ⟨-, -, h3⟩ := Orb.permOK_facts h
  exact bij_of (fun x hx => (h3 x hx).1) (fun x hx => (h3 x hx).2)

theorem lsz : lGens.size = 3 := by simp [lGens, ruLGensA_size]

theorem lgens : ∀ k < lGens.size, TR 4060 lGens[k]! (apP (RuW.LG k)) ∧
    TR 4060 lGensInv[k]! (apP (RuW.LGI k)) ∧ Bij 4060 (apP (RuW.LG k)) (apP (RuW.LGI k)) := by
  intro k hk
  rw [lsz] at hk
  have hk' : k < ruLGensA.size := by rw [ruLGensA_size]; exact hk
  have e1 : lGens[k]! = tblOfArr (unpack 4060 12 (RuW.LG k)) := by
    rw [lGens, getElem!_pos _ k (by simpa using hk'), Array.getElem_map,
      ← getElem!_pos ruLGensA k hk', RuW.lg_eq hk]
  have e2 : lGensInv[k]! = tblOfArr (unpack 4060 12 (RuW.LGI k)) := by
    rw [lGensInv, getElem!_pos _ k (by simpa using hk'), Array.getElem_map, Array.getElem_map,
      ← getElem!_pos ruLGensA k hk', (RuG.inv_of (RuW.lg_eq hk) (RuW.lgi hk)).1]
  refine ⟨?_, ?_, bij_of_pk (RuW.lgi hk)⟩
  · rw [e1]
    exact tr_unpack _
  · rw [e2]
    exact tr_unpack _

theorem key (y : Fin 4060) : apP GP (apP HP (apP GIP (apP HIP y))) = ruTZ 108 y := by
  have hT := pw_prep RuI.hPL (RuI.prep_of RuG.a0_eq rep_ruA0) (RuI.prep_of RuG.a1_eq rep_ruA1)
    64 108 (by decide)
  have hc := comm
  simp only [PackFld.strictB_eqP] at hc
  exact commK_sound hT (RuI.prep_of RuG.z_eq rep_ruZ) hc y

theorem pairCheck : ruPairCheck = true := by
  have hn : (4060 : Nat) < 2 ^ 32 := by decide
  have wg : lettersOK lGens.size pairWordG = true := by rw [lsz]; decide
  have wh : lettersOK lGens.size pairWordH = true := by rw [lsz]; decide
  have tG := (tr_word lgens pairWordG wg).1
  have tH := (tr_word lgens pairWordH wh).1
  have hpG := pG
  have hpH := pH
  simp only [PackFld.strictB_eqP] at hpG hpH
  have bG := bij_of_pk hpG
  have bH := bij_of_pk hpH
  have tGI := tr_invT hn tG bG
  have tHI := tr_invT hn tH bH
  have tK := tr_compT (tr_compT (tr_compT tG tH bH.1) tGI bG.2.1) tHI bH.2.1
  have hR := rep_ruTZ 108
  have tR := tr_tblOfArr (n := 4060) (a := ruTZA 108) (by simp [ruTZA, CFSG.Monster.B.Co2.Native.compA])
    (fun x hx => by
      rw [hR ⟨x, hx⟩]
      exact Nat.lt_trans (ruTZ 108 ⟨x, hx⟩).2 (by decide))
  have e15 : ruRepZA 15 = ruTZA 108 := rfl
  simp only [ruPairCheck, pairTabG, pairTabH, Bool.and_eq_true]
  refine ⟨⟨invOK_of tG tGI bG, invOK_of tH tHI bH⟩, ?_⟩
  unfold CFSG.Sporadic.Schreier.Native.tblEq
  rw [allIn_iff, e15]
  intro y hy
  have k1 := tK.2 y hy
  have k2 := tR.2 y hy
  have k3 := key ⟨y, hy⟩
  have k4 := hR ⟨y, hy⟩
  simp only at k1 k2 k3 k4
  rw [k1, k2, k4, ← k3]
  exact beq_self_eq_true _

end CertificateChecks.KernelSporSch.RuPair

end
