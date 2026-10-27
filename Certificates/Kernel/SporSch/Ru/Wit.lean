module

public import Certificates.Kernel.SporSch.Ru.WitData
public import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def rowM (t : Nat) : Bool := rowOK (encRows ruMProg) VM t

@[expose] noncomputable def rwok (q : Nat) : Bool :=
  wordAppK 4060 12 (mask 12) (gen2 M1 M2) (gen2 M1I M2I) 2
    (takeK 10 (dropK (10 * q) ruRMWord)) (RwP (q + 1)) (RwP q)

@[expose] noncomputable def lgok (k : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 M1 M2) (gen2 M1I M2I) 2
      (dword ruLMWords 0 k) (LM k),
    bAnd(compEqK 4060 12 (mask 12) (4060 * 12) Hw (LM k) (HLM k),
    bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (HLM k) HwI (LG k), pk (LG k) (LGI k))))

@[expose] noncomputable def fgok (k : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 A0 A1) (gen2 A0I A1I) 2
    (ruFusRec (k + 1)).2.1 (FG k), pk (FG k) (FGI k))

end CertificateChecks.KernelSporSch.RuW

#kss_each CertificateChecks.KernelSporSch.RuW.RM CertificateChecks.KernelSporSch.RuW.rowM 11
#kss_each CertificateChecks.KernelSporSch.RuW.RWC CertificateChecks.KernelSporSch.RuW.rwok 6
#kss_each CertificateChecks.KernelSporSch.RuW.LGC CertificateChecks.KernelSporSch.RuW.lgok 3
#kss_each CertificateChecks.KernelSporSch.RuW.FGC CertificateChecks.KernelSporSch.RuW.fgok 3

namespace CertificateChecks.KernelSporSch.RuW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

theorem finM : bAnd(finOK (encRows ruMProg) 11 VM M1 M2,
    bAnd(Nat.beq (VM 0) A0, Nat.beq (VM 1) A1)) = true := by quickRfl

theorem pM1 : pk M1 M1I = true := by quickRfl
theorem pM2 : pk M2 M2I = true := by quickRfl
theorem rwEnd : Nat.beq (RwP 6) (pidn 4060 12) = true := by quickRfl
theorem rwStart : Nat.beq (RwP 0) Rw = true := by quickRfl

theorem wwW : wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 A0 A1) (gen2 A0I A1I) 2
    ruAlignmentSeedWord Ww = true := by quickRfl

theorem pWw : pk Ww WwI = true := by quickRfl
theorem pHw : pk Hw HwI = true := by quickRfl
theorem cWR : compEqK 4060 12 (mask 12) (4060 * 12) Ww Rw WR = true := by quickRfl
theorem cWRWI : compEqK 4060 12 (mask 12) (4060 * 12) WR WwI WRWI = true := by quickRfl
theorem cUw : compEqK 4060 12 (mask 12) (4060 * 12) WRWI A0 Uw = true := by quickRfl
theorem u7 : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) Uw 7 U7 = true := by quickRfl
theorem cHw : compEqK 4060 12 (mask 12) (4060 * 12) U7 Ww Hw = true := by quickRfl

theorem mRun : ruMRunA = (unpack 4060 12 M1, unpack 4060 12 M2, true) := slot_eq rfl rfl RM.all finM

theorem m1_eq : ruM1A = unpack 4060 12 M1 := by rw [ruM1A, mRun]
theorem m2_eq : ruM2A = unpack 4060 12 M2 := by rw [ruM2A, mRun]

theorem rw_eq : ruRwA = unpack 4060 12 Rw := by
  rw [ruRwA, ruMWordA]
  refine (congrArg (fun T => wordA 4060 #[ruM1A, ruM2A] T ruRMWord) (invs2 ruM1A ruM2A)).trans ?_
  refine Eq.trans ?_ (congrArg (unpack 4060 12) (Nat.eq_of_beq_eq_true rwStart))
  have hlen : ruRMWord.length ≤ 10 * 6 := by decide
  refine chunks_eq (f := fun l => wordA 4060 #[ruM1A, ruM2A] (rawInvs 4060 #[ruM1A, ruM2A]) l)
    (wd := ruRMWord) (c := 10) (K := 6) (P := fun q => unpack 4060 12 (RwP q))
    hlen ?_ fun q hq ih => ?_
  · have e : wordA 4060 #[ruM1A, ruM2A] (rawInvs 4060 #[ruM1A, ruM2A]) [] = idA 4060 := rfl
    refine e.trans ?_
    rw [Nat.eq_of_beq_eq_true rwEnd, idK_sound idOK]
  · have h := RWC.all q hq
    unfold rwok at h
    rw [takeK_eq, dropK_eq] at h
    exact wordAppK_sound (binds2 m1_eq m2_eq) (perms2 pM1 pM2) ih h

theorem ww_eq : ruWwA = unpack 4060 12 Ww := by
  rw [ruWwA, ruSeedWordA]
  exact (congrArg (fun T => wordA 4060 #[ruA0A, ruA1A] T ruAlignmentSeedWord)
    (invs2 ruA0A ruA1A)).trans (wordEqK_sound (binds2 a0_eq a1_eq) (perms2 pA0 pA1) wwW).1

theorem wwi_eq : ruInv ruWwA = unpack 4060 12 WwI := by
  rw [ww_eq]
  exact (inv_of rfl pWw).1

theorem uw_eq : ruUwA = unpack 4060 12 Uw := by
  rw [ruUwA, wwi_eq, ww_eq, rw_eq, a0_eq, compEqK_sound cWR, compEqK_sound cWRWI,
    compEqK_sound cUw]

theorem hw_eq : ruHwA = unpack 4060 12 Hw := by
  rw [ruHwA, uw_eq, powEqRK_sound u7, ww_eq, compEqK_sound cHw]

theorem hwi_eq : ruInv ruHwA = unpack 4060 12 HwI := by
  rw [hw_eq]
  exact (inv_of rfl pHw).1

theorem lg_eq {k : Nat} (hk : k < 3) : ruLGensA[k]! = unpack 4060 12 (LG k) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (LGC.all k hk)
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, _⟩ := (bAnd_iff _ _).1 h4
  have hw := (wordEqK_sound (binds2 m1_eq m2_eq) (perms2 pM1 pM2) h1).1
  rw [← invs2, dword_zero] at hw
  rw [← compEqK_sound h5, ← compEqK_sound h3, ← hw, ← hw_eq, ← hwi_eq, ruLGensA,
    getElem!_pos _ k (by simp [ruLMWords]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ruLMWords]; omega),
    Option.getD_some, ruMWordA]

theorem lgi {k : Nat} (hk : k < 3) : pk (LG k) (LGI k) = true := by
  obtain ⟨_, h2⟩ := (bAnd_iff _ _).1 (LGC.all k hk)
  obtain ⟨_, h4⟩ := (bAnd_iff _ _).1 h2
  exact ((bAnd_iff _ _).1 h4).2

theorem fg_eq {k : Nat} (hk : k < 3) : ruFusGA (k + 1) = unpack 4060 12 (FG k) := by
  obtain ⟨h1, _⟩ := (bAnd_iff _ _).1 (FGC.all k hk)
  rw [ruFusGA, ruSeedWordA]
  exact (congrArg (fun T => wordA 4060 #[ruA0A, ruA1A] T (ruFusRec (k + 1)).2.1)
    (invs2 ruA0A ruA1A)).trans (wordEqK_sound (binds2 a0_eq a1_eq) (perms2 pA0 pA1) h1).1

theorem fgi {k : Nat} (hk : k < 3) : pk (FG k) (FGI k) = true :=
  ((bAnd_iff _ _).1 (FGC.all k hk)).2

theorem l1 : lettersK 2 ruRMWord = true := by quickRfl
theorem l2 : lettersK 2 ruAlignmentSeedWord = true := by quickRfl
theorem l3 : lettersAllK 2 ruLMWords = true := by quickRfl

theorem facts : ruMRunA.2.2 = true ∧ isInvA 4060 ruM1A (ruInv ruM1A) = true ∧
    isInvA 4060 ruM2A (ruInv ruM2A) = true ∧ isInvA 4060 ruWwA (ruInv ruWwA) = true ∧
    isInvA 4060 ruHwA (ruInv ruHwA) = true ∧
    (∀ i < 3, isInvA 4060 ruLGensA[i]! (ruInv ruLGensA[i]!) = true) ∧
    (∀ i ∈ [1, 2, 3], isInvA 4060 (ruFusGA i) (ruInv (ruFusGA i)) = true) ∧
    lettersOK 2 ruRMWord = true ∧ lettersOK 2 ruAlignmentSeedWord = true ∧
    ruLMWords.all (lettersOK 2) = true ∧
    (∀ i ∈ [1, 2, 3], lettersOK 4 (ruFusRec i).1 = true ∧ lettersOK 2 (ruFusRec i).2.1 = true) ∧
    (∀ p ∈ [5, 7, 13], lettersOK 3 (ruObsRec p).1 = true) ∧
    ruSylowFusion.map (fun r => r.2.2) = [7, 5, 7] ∧
    ruOddNormalObstructions.map (fun r => r.1) = [5, 7, 13] ∧
    ruOddNormalObstructions.map (fun r => r.2.2) = [3, 3, 3] := by
  refine ⟨by rw [mRun], (inv_of m1_eq pM1).2, (inv_of m2_eq pM2).2, (inv_of ww_eq pWw).2,
    (inv_of hw_eq pHw).2, fun i hi => (inv_of (lg_eq hi) (lgi hi)).2, fun i hi => ?_,
    lettersK_sound l1, lettersK_sound l2, lettersAllK_sound l3, by decide, by decide, by decide,
    by decide, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact (inv_of (fg_eq (k := 0) (by omega)) (fgi (by omega))).2
  · exact (inv_of (fg_eq (k := 1) (by omega)) (fgi (by omega))).2
  · exact (inv_of (fg_eq (k := 2) (by omega)) (fgi (by omega))).2

end CertificateChecks.KernelSporSch.RuW

end
