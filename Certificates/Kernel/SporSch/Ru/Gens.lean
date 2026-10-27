module

public import Certificates.Kernel.SporSch.Ru.GensData
public import Certificates.Kernel.SporSch.Ru.Lines
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

@[expose] noncomputable def A0 : Nat := RuT4060.L 0

@[expose] noncomputable def A1 : Nat := RuT4060.L 1

@[expose] noncomputable def pk (p q : Nat) : Bool := permOK 4060 12 (mask 12) (4060 * 12) p q

@[expose] noncomputable def rowC (t : Nat) : Bool := rowOK (encRows ruCProg) VC t

@[expose] noncomputable def rowN (t : Nat) : Bool := rowOK (encRows ruNProg) VN t

end CertificateChecks.KernelSporSch.RuG

#kss_each CertificateChecks.KernelSporSch.RuG.RC CertificateChecks.KernelSporSch.RuG.rowC 20
#kss_each CertificateChecks.KernelSporSch.RuG.RN CertificateChecks.KernelSporSch.RuG.rowN 15

namespace CertificateChecks.KernelSporSch.RuG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem finC : bAnd(finOK (encRows ruCProg) 20 VC C0 C1,
    bAnd(Nat.beq (VC 0) A0, Nat.beq (VC 1) A1)) = true := by quickRfl

theorem finN : bAnd(finOK (encRows ruNProg) 15 VN N0 N1,
    bAnd(Nat.beq (VN 0) A0, Nat.beq (VN 1) A1)) = true := by quickRfl

theorem pA0 : pk A0 A0I = true := by quickRfl
theorem pA1 : pk A1 A1I = true := by quickRfl
theorem pC0 : pk C0 C0I = true := by quickRfl
theorem pC1 : pk C1 C1I = true := by quickRfl
theorem pN0 : pk N0 N0I = true := by quickRfl
theorem pN1 : pk N1 N1I = true := by quickRfl
theorem pH : pk H HI = true := by quickRfl
theorem pNs0 : pk Ns0 Ns0I = true := by quickRfl
theorem pNs1 : pk Ns1 Ns1I = true := by quickRfl
theorem pW : invEqK 4060 12 (mask 12) (4060 * 12) W WI = true := by quickRfl
theorem pHI : invEqK 4060 12 (mask 12) (4060 * 12) H HI = true := by quickRfl

theorem zC : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) C0 10 Z = true := by quickRfl

theorem wW : wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 A0 A1)
    (gen2 A0I A1I) 2 ruSeedWord W = true := by
  quickRfl

@[expose] noncomputable def z0ok (q : Nat) : Bool :=
  wordAppK 4060 12 (mask 12) (gen2 N0 N1) (gen2 N0I N1I) 2
    (takeK 10 (dropK (10 * q) ruNCenterWord)) (Z0P (q + 1)) (Z0P q)

end CertificateChecks.KernelSporSch.RuG

#kss_each CertificateChecks.KernelSporSch.RuG.Z0C CertificateChecks.KernelSporSch.RuG.z0ok 21

namespace CertificateChecks.KernelSporSch.RuG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem z0end : Nat.beq (Z0P 21) (pidn 4060 12) = true := by quickRfl

theorem z0start : Nat.beq (Z0P 0) Z0 = true := by quickRfl

theorem idOK : idK 4060 12 (mask 12) = true := by quickRfl

theorem cWZ0 : compEqK 4060 12 (mask 12) (4060 * 12) W Z0 WZ0 = true := by quickRfl
theorem cWZ0WI : compEqK 4060 12 (mask 12) (4060 * 12) WZ0 WI WZ0WI = true := by quickRfl
theorem cU : compEqK 4060 12 (mask 12) (4060 * 12) WZ0WI Z U = true := by quickRfl
theorem u3 : powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) U 3 U3 = true := by quickRfl
theorem cH : compEqK 4060 12 (mask 12) (4060 * 12) U3 W H = true := by quickRfl
theorem cHN0 : compEqK 4060 12 (mask 12) (4060 * 12) H N0 HN0 = true := by quickRfl
theorem cHN1 : compEqK 4060 12 (mask 12) (4060 * 12) H N1 HN1 = true := by quickRfl
theorem cNs0 : compEqK 4060 12 (mask 12) (4060 * 12) HN0 HI Ns0 = true := by quickRfl
theorem cNs1 : compEqK 4060 12 (mask 12) (4060 * 12) HN1 HI Ns1 = true := by quickRfl

@[expose] noncomputable def sgOK (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 Ns0 Ns1)
    (gen2 Ns0I Ns1I) 2 (dword ruSWords 0 i) (SG i)

theorem sg0 : sgOK 0 = true := by quickRfl
theorem sg1 : sgOK 1 = true := by quickRfl
theorem sg2 : sgOK 2 = true := by quickRfl
theorem sg3 : sgOK 3 = true := by quickRfl
theorem pSG : allN 4 (fun i => pk (SG i) (SGI i)) = true := by quickRfl

theorem a0_eq : ruA0A = unpack 4060 12 A0 := row4060 (by omega)
theorem a1_eq : ruA1A = unpack 4060 12 A1 := row4060 (by omega)

theorem inv_of {a : Array Nat} {P PI : Nat} (ha : a = unpack 4060 12 P) (h : pk P PI = true) :
    ruInv a = unpack 4060 12 PI ∧ isInvA 4060 a (ruInv a) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := PI) h
  rw [ruInv, ha, h1]
  exact ⟨rfl, h2⟩

theorem slot_eq {rows : List SlotRow} {V : Nat → Nat} {L C D : Nat} (hL : rows.length = L)
    (hL' : Nat.blt L 999999 = true)
    (hr : ∀ t < L, rowOK (encRows rows) V t = true)
    (hf : bAnd(finOK (encRows rows) L V C D, bAnd(Nat.beq (V 0) A0, Nat.beq (V 1) A1)) = true) :
    slotRunA 4060 rows ruA0A ruA1A = (unpack 4060 12 C, unpack 4060 12 D, true) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hf
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  have e0 := Nat.eq_of_beq_eq_true h3
  have e1 := Nat.eq_of_beq_eq_true h4
  rw [a0_eq, a1_eq, ← e0, ← e1]
  exact slotV_sound hL (Nat.blt_eq.mp hL') (by rw [e0]; exact pA0) (by rw [e1]; exact pA1) hr h1

theorem cRun : ruCRunA = (unpack 4060 12 C0, unpack 4060 12 C1, true) := slot_eq rfl rfl RC.all finC
theorem nRun : ruNRunA = (unpack 4060 12 N0, unpack 4060 12 N1, true) := slot_eq rfl rfl RN.all finN

theorem c0_eq : ruC0A = unpack 4060 12 C0 := by rw [ruC0A, cRun]
theorem c1_eq : ruC1A = unpack 4060 12 C1 := by rw [ruC1A, cRun]
theorem n0_eq : ruN0A = unpack 4060 12 N0 := by rw [ruN0A, nRun]
theorem n1_eq : ruN1A = unpack 4060 12 N1 := by rw [ruN1A, nRun]

theorem z_eq : ruZA = unpack 4060 12 Z := by
  rw [ruZA, c0_eq]
  exact powEqRK_sound zC

theorem binds2 {a b : Array Nat} {P Q : Nat} (ha : a = unpack 4060 12 P)
    (hb : b = unpack 4060 12 Q) :
    (#[a, b] : Array (Array Nat)).size = 2 ∧ ∀ j < 2, (#[a, b] : Array (Array Nat))[j]! =
      unpack 4060 12 (gen2 P Q j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rcases j with _ | _ | j
  · exact ha
  · exact hb
  · omega

theorem perms2 {P Q PI QI : Nat} (hP : pk P PI = true) (hQ : pk Q QI = true) :
    allN 2 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (gen2 P Q j) (gen2 PI QI j)) = true := by
  have e : ∀ f : Nat → Bool, f 0 = true → f 1 = true → allN 2 f = true := fun f h0 h1 => by
    change bAnd(allBlk 0 f 2, true) = true
    change bAnd(bAnd(f (Nat.add 0 1), bAnd(f (Nat.add 0 0), true)), true) = true
    simp [h0, h1]
  exact e _ hP hQ

theorem invs2 (a b : Array Nat) : (#[ruInv a, ruInv b] : Array (Array Nat)) =
    rawInvs 4060 #[a, b] := by
  simp [rawInvs, ruInv]

theorem w_eq : ruWA = unpack 4060 12 W := by
  rw [ruWA]
  exact (congrArg (fun T => wordA 4060 #[ruA0A, ruA1A] T ruSeedWord) (invs2 ruA0A ruA1A)).trans
    (wordEqK_sound (binds2 a0_eq a1_eq) (perms2 pA0 pA1) wW).1

theorem z0_eq : ruZ0A = unpack 4060 12 Z0 := by
  rw [ruZ0A]
  refine (congrArg (fun T => wordA 4060 #[ruN0A, ruN1A] T ruNCenterWord)
    (invs2 ruN0A ruN1A)).trans ?_
  refine Eq.trans ?_ (congrArg (unpack 4060 12) (Nat.eq_of_beq_eq_true z0start))
  have hc : ∀ q < 21, z0ok q = true := Z0C.all
  have hlen : ruNCenterWord.length ≤ 10 * 21 := by decide
  refine chunks_eq (f := fun l => wordA 4060 #[ruN0A, ruN1A] (rawInvs 4060 #[ruN0A, ruN1A]) l)
    (wd := ruNCenterWord) (c := 10) (K := 21) (P := fun q => unpack 4060 12 (Z0P q))
    hlen ?_ fun q hq ih => ?_
  · have e : wordA 4060 #[ruN0A, ruN1A] (rawInvs 4060 #[ruN0A, ruN1A]) [] = idA 4060 := rfl
    refine e.trans ?_
    rw [Nat.eq_of_beq_eq_true z0end, idK_sound idOK]
  · have h := hc q hq
    unfold z0ok at h
    rw [takeK_eq, dropK_eq] at h
    exact wordAppK_sound (binds2 n0_eq n1_eq) (perms2 pN0 pN1) ih h

theorem wi_eq : ruInv ruWA = unpack 4060 12 WI := by
  rw [ruInv, w_eq]
  exact (invEqK_sound pW).1

theorem u_eq : ruUA = unpack 4060 12 U := by
  rw [ruUA, wi_eq, w_eq, z0_eq, z_eq, compEqK_sound cWZ0, compEqK_sound cWZ0WI,
    compEqK_sound cU]

theorem h_eq : ruHA = unpack 4060 12 H := by
  rw [ruHA, u_eq, powEqRK_sound u3, w_eq, compEqK_sound cH]

theorem hi_eq : ruInv ruHA = unpack 4060 12 HI := by
  rw [ruInv, h_eq]
  exact (invEqK_sound pHI).1

theorem ns0_eq : ruNs0A = unpack 4060 12 Ns0 := by
  rw [ruNs0A, hi_eq, h_eq, n0_eq, compEqK_sound cHN0, compEqK_sound cNs0]

theorem ns1_eq : ruNs1A = unpack 4060 12 Ns1 := by
  rw [ruNs1A, hi_eq, h_eq, n1_eq, compEqK_sound cHN1, compEqK_sound cNs1]

theorem dword_zero : ∀ (D : List (List Int)) (j : Nat), dword D 0 j = D.getD j []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: D, j + 1 => dword_zero D j

theorem sg_eq {i : Nat} (hi : i < 4) : ruSGensA[i]! = unpack 4060 12 (SG i) := by
  have hs : sgOK i = true := by
    rcases i with _ | _ | _ | _ | i
    exacts [sg0, sg1, sg2, sg3, absurd hi (by omega)]
  have h := (wordEqK_sound (binds2 ns0_eq ns1_eq) (perms2 pNs0 pNs1) hs).1
  rw [← invs2, dword_zero] at h
  rw [← h, ruSGensA, getElem!_pos _ i (by simp [ruSWords]; omega)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ruSWords]; omega),
    Option.getD_some]

theorem basic : isInvA 4060 ruA0A (ruInv ruA0A) = true ∧ isInvA 4060 ruA1A (ruInv ruA1A) = true ∧
    ruCRunA.2.2 = true ∧ ruNRunA.2.2 = true ∧ isInvA 4060 ruN0A (ruInv ruN0A) = true ∧
    isInvA 4060 ruN1A (ruInv ruN1A) = true ∧ isInvA 4060 ruC0A (ruInv ruC0A) = true ∧
    isInvA 4060 ruC1A (ruInv ruC1A) = true ∧ isInvA 4060 ruWA (ruInv ruWA) = true ∧
    isInvA 4060 ruHA (ruInv ruHA) = true ∧ isInvA 4060 ruNs0A (ruInv ruNs0A) = true ∧
    isInvA 4060 ruNs1A (ruInv ruNs1A) = true ∧
    (∀ i < 4, isInvA 4060 ruSGensA[i]! (ruInv ruSGensA[i]!) = true) := by
  refine ⟨(inv_of a0_eq pA0).2, (inv_of a1_eq pA1).2, by rw [cRun], by rw [nRun],
    (inv_of n0_eq pN0).2, (inv_of n1_eq pN1).2, (inv_of c0_eq pC0).2, (inv_of c1_eq pC1).2, ?_,
    (inv_of h_eq pH).2, (inv_of ns0_eq pNs0).2, (inv_of ns1_eq pNs1).2,
    fun i hi => (inv_of (sg_eq hi) (allN_spec pSG i hi)).2⟩
  rw [wi_eq, w_eq]
  exact (invEqK_sound pW).2

end CertificateChecks.KernelSporSch.RuG

end
