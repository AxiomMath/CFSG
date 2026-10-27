module

public import Certificates.Kernel.SporSch.Ru.TMem27100
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.PermToolSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TMem27100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34K CFSG.KC.L34KSnd
open CertificateChecks.KernelSporSch.RuG CFSG.EvenSporadicStandard.Induction.TMemRu
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier CFSG.PSL3Four.Native CFSG.Certificates.Native
open CFSG.KLie.CT (andB orB notB)

attribute [local irreducible] idTab idA ruA0A ruA1A

abbrev Cn (p : Nat) : Prop := canonK 4060 12 (mask 12) (4060 * 12) p = true

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem hsz : szOK 4060 12 = true := by decide

theorem cE : Cn e := canon_pidn hsz

theorem hidA : idA 4060 = unpack 4060 12 e := (idK_sound idOK).symm

theorem hidT : idTab 4060 = unpack 4060 12 e := idTab_unpack' hsz

theorem cpc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem comp_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 4060 (unpack 4060 12 p) (unpack 4060 12 q) = unpack 4060 12 (pc p q) :=
  comp_unpack' hp hq

theorem compA_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 4060 (unpack 4060 12 p) (unpack 4060 12 q) = unpack 4060 12 (pc p q) := by
  rw [← CFSG.KC.PermTool.comp_eq]
  exact comp_u hp hq

theorem eqA_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    eqA 4060 (unpack 4060 12 p) (unpack 4060 12 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

theorem beq_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 4060 12 p == unpack 4060 12 q) = Nat.beq p q := CFSG.KC.L34KSnd.beq_unpack hp hq

theorem kC : andB (cn A0) (andB (cn A1) (andB (cn A0I) (cn A1I))) = true := by quickRfl

theorem kL : andB (lettersK 2 tmWordA) (andB (lettersK 2 tmWordB) (andB (lettersK 2 tmWordL)
    (andB (lettersK 2 tmWordZ) (andB (lettersK 4 tmWordG0) (andB (lettersK 4 tmWordG1)
    (andB (allN 4 fun i => lettersK 2 (tmWordsS.getD i []))
      (allN 7 fun j => lettersK 2 (tmWordsC.getD j [])))))))) = true := by
  quickRfl

theorem gens_c : Cn A0 ∧ Cn A1 ∧ Cn A0I ∧ Cn A1I := by
  have h := kC
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h
  exact ⟨h1, h2, h3, h4⟩

theorem letters : lettersK 2 tmWordA = true ∧ lettersK 2 tmWordB = true ∧
    lettersK 2 tmWordL = true ∧ lettersK 2 tmWordZ = true ∧ lettersK 4 tmWordG0 = true ∧
    lettersK 4 tmWordG1 = true ∧ (∀ i < 4, lettersK 2 (tmWordsS.getD i []) = true) ∧
    ∀ j < 7, lettersK 2 (tmWordsC.getD j []) = true := by
  have h := kL
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h8⟩ := andB_iff.1 h
  exact ⟨h1, h2, h3, h4, h5, h6, fun i hi => CFSG.KS.Raw.Orb.allN_iff.1 h7 i hi,
    fun j hj => CFSG.KS.Raw.Orb.allN_iff.1 h8 j hj⟩

theorem ok_spec {p : Nat} (h : ok p = true) : Cn p ∧ Cn (pinv p) ∧ pk p (pinv p) = true := by
  unfold ok at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  exact ⟨h1, h2, h3⟩

theorem inv_parts : (Cn TA ∧ Cn TAI ∧ pk TA TAI = true) ∧ (Cn TB ∧ Cn TBI ∧ pk TB TBI = true) ∧
    (Cn TL ∧ Cn TLI ∧ pk TL TLI = true) ∧ (Cn TAl ∧ Cn TAlI ∧ pk TAl TAlI = true) ∧
    (Cn TBl ∧ Cn TBlI ∧ pk TBl TBlI = true) ∧ Cn TZ ∧
    (∀ i < 4, Cn (SG i) ∧ Cn (pinv (SG i)) ∧ pk (SG i) (pinv (SG i)) = true) ∧
    (∀ j < 7, Cn (CG j) ∧ Cn (pinv (CG j)) ∧ pk (CG j) (pinv (CG j)) = true) := by
  have h := kInv
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h8⟩ := andB_iff.1 h
  exact ⟨ok_spec h1, ok_spec h2, ok_spec h3, ok_spec h4, ok_spec h5, h6,
    fun i hi => ok_spec (CFSG.KS.Raw.Orb.allN_iff.1 h7 i hi),
    fun j hj => ok_spec (CFSG.KS.Raw.Orb.allN_iff.1 h8 j hj)⟩

theorem word_of {S : Array (Array Nat)} {k : Nat} {PS PSI : Nat → Nat} {wd : List Int}
    (hS : S.size = k ∧ ∀ j < k, S[j]! = unpack 4060 12 (PS j))
    (hp : ∀ j < k, pk (PS j) (PSI j) = true) (hl : lettersK k wd = true) :
    wordA 4060 S (rawInvs 4060 S) wd = unpack 4060 12 (wordK 4060 12 (mask 12) e PS PSI wd) := by
  refine (wordEqK_sound hS (CFSG.KS.Raw.Orb.allN_iff.2 hp) ?_).1
  unfold wordEqK
  simp only [bAnd_iff, hsz, hl, true_and]
  exact Nat.beq_refl _

theorem a0_c : ruA0A = unpack 4060 12 A0 := a0_eq
theorem a1_c : ruA1A = unpack 4060 12 A1 := a1_eq

theorem gen2_bind : tmGen2.size = 2 ∧ ∀ j < 2, tmGen2[j]! = unpack 4060 12 (sel2 A0 A1 j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => exact a0_c
  | 1, _ => exact a1_c

theorem gen2_p : ∀ j < 2, pk (sel2 A0 A1 j) (sel2 A0I A1I j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact pA0
  | 1, _ => exact pA1

theorem gen2i_eq : tmGen2i = rawInvs 4060 tmGen2 := by
  simp [rawInvs, tmGen2, tmGen2i, ruInv]

theorem tA_eq : tmTA = unpack 4060 12 TA := by
  unfold tmTA TA W2
  rw [gen2i_eq, word_of gen2_bind gen2_p letters.1]

theorem tB_eq : tmTB = unpack 4060 12 TB := by
  unfold tmTB TB W2
  rw [gen2i_eq, word_of gen2_bind gen2_p letters.2.1]

theorem tL_eq : tmTL = unpack 4060 12 TL := by
  unfold tmTL TL W2
  rw [gen2i_eq, word_of gen2_bind gen2_p letters.2.2.1]

theorem inv_u {a : Array Nat} {P : Nat} (ha : a = unpack 4060 12 P) (h : pk P (pinv P) = true) :
    ruInv a = unpack 4060 12 (pinv P) ∧ isInvA 4060 a (ruInv a) = true := inv_of ha h

theorem genAB_bind : tmGenAB.size = 2 ∧ ∀ j < 2, tmGenAB[j]! = unpack 4060 12 (sel2 TA TB j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => exact tA_eq
  | 1, _ => exact tB_eq

theorem genAB_p : ∀ j < 2, pk (sel2 TA TB j) (sel2 TAI TBI j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact inv_parts.1.2.2
  | 1, _ => exact inv_parts.2.1.2.2

theorem genABi_eq : tmGenABi = rawInvs 4060 tmGenAB := by
  simp [rawInvs, tmGenAB, tmGenABi, ruInv]

theorem tZ_eq : tmTZ = unpack 4060 12 TZ := by
  unfold tmTZ TZ WAB
  rw [genABi_eq, word_of genAB_bind genAB_p letters.2.2.2.1]

theorem sG_eq {i : Nat} (hi : i < 4) : tmSGen i = unpack 4060 12 (SG i) := by
  unfold tmSGen SG WAB
  rw [genABi_eq, word_of genAB_bind genAB_p (letters.2.2.2.2.2.2.1 i hi)]

theorem cG_eq {j : Nat} (hj : j < 7) : tmCGen j = unpack 4060 12 (CG j) := by
  unfold tmCGen CG WAB
  rw [genABi_eq, word_of genAB_bind genAB_p (letters.2.2.2.2.2.2.2 j hj)]

theorem tLi_eq : ruInv tmTL = unpack 4060 12 TLI := (inv_u tL_eq inv_parts.2.2.1.2.2).1

theorem tAl_eq : tmTAl = unpack 4060 12 TAl := by
  obtain ⟨cA, -, -⟩ := inv_parts.1
  obtain ⟨cL, cLI, -⟩ := inv_parts.2.2.1
  unfold tmTAl
  rw [tL_eq, tA_eq, ← tL_eq, tLi_eq, tL_eq, compA_u cL cA, compA_u (cpc cL cA) cLI]
  rfl

theorem tBl_eq : tmTBl = unpack 4060 12 TBl := by
  obtain ⟨cB, -, -⟩ := inv_parts.2.1
  obtain ⟨cL, cLI, -⟩ := inv_parts.2.2.1
  unfold tmTBl
  rw [tL_eq, tB_eq, ← tL_eq, tLi_eq, tL_eq, compA_u cL cB, compA_u (cpc cL cB) cLI]
  rfl

theorem gen4_bind : tmGen4.size = 4 ∧
    ∀ j < 4, tmGen4[j]! = unpack 4060 12 (sel4 TA TB TAl TBl j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => exact tA_eq
  | 1, _ => exact tB_eq
  | 2, _ => exact tAl_eq
  | 3, _ => exact tBl_eq

theorem gen4_p : ∀ j < 4, pk (sel4 TA TB TAl TBl j) (sel4 TAI TBI TAlI TBlI j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact inv_parts.1.2.2
  | 1, _ => exact inv_parts.2.1.2.2
  | 2, _ => exact inv_parts.2.2.2.1.2.2
  | 3, _ => exact inv_parts.2.2.2.2.1.2.2

theorem gen4i_eq : tmGen4i = rawInvs 4060 tmGen4 := by
  simp [rawInvs, tmGen4, tmGen4i, ruInv]

theorem ppow_succ (p k : Nat) :
    ppow 4060 12 (mask 12) e p (k + 1) = pc p (ppow 4060 12 (mask 12) e p k) := by
  change strictN (ppow 4060 12 (mask 12) e p k) (fun q => pcomp 4060 12 (mask 12) p q) = _
  exact strictN_app' _ _

theorem powA_u {p : Nat} (hp : Cn p) : ∀ k,
    powA 4060 (unpack 4060 12 p) k = unpack 4060 12 (ppow 4060 12 (mask 12) e p k) ∧
      Cn (ppow 4060 12 (mask 12) e p k)
  | 0 => ⟨hidA, cE⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := powA_u hp k
    rw [ppow_succ]
    refine ⟨?_, cpc hp ih2⟩
    change compA 4060 (unpack 4060 12 p) (powA 4060 (unpack 4060 12 p) k) = _
    rw [ih1, compA_u hp ih2]

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · have h' : Nat.beq a b = false := by
      cases h2 : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h2) h
    rw [h']
    exact beq_false_of_ne h

theorem notB_beq {a b : Nat} (h : notB (Nat.beq a b) = true) : Nat.beq a b = false := notB_iff.1 h

theorem basic : tmBasicCheck = true := by
  have cA0 := gens_c.1
  have h := kBasic
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  have i0 := inv_of a0_eq pA0
  have i1 := inv_of a1_eq pA1
  have e1 : eqA 4060 (compA 4060 ruA0A ruA0A) (idA 4060) = true := by
    rw [a0_c, compA_u cA0 cA0, hidA, eqA_u (cpc cA0 cA0) cE]
    exact h1
  have e2 : eqA 4060 ruA0A (idA 4060) = false := by
    rw [a0_c, hidA, eqA_u cA0 cE]
    exact notB_beq h2
  have e3 : allLt 4060 (fun i => ruA0A[i]! != i) = true := by
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    rw [a0_c, CFSG.KC.BfsPin.unpack_get' hi, bne, beq_nat, notB_beq (CFSG.KS.Raw.Orb.allN_iff.1 h3 i hi)]
    rfl
  unfold tmBasicCheck
  simp only [i0.2, i1.2, e1, e2, e3, Bool.true_and, Bool.and_true, Bool.not_false]
  decide

theorem ab : tmABCheck = true := by
  have cA0 := gens_c.1
  obtain ⟨cA, -, pA⟩ := inv_parts.1
  obtain ⟨cB, -, pB⟩ := inv_parts.2.1
  have h := kAB
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h8⟩ := andB_iff.1 h
  have iA := inv_u tA_eq pA
  have iB := inv_u tB_eq pB
  have m1 : eqA 4060 (compA 4060 tmTA ruA0A) (compA 4060 ruA0A tmTA) = true := by
    rw [tA_eq, a0_c, compA_u cA cA0, compA_u cA0 cA, eqA_u (cpc cA cA0) (cpc cA0 cA)]
    exact h1
  have m2 : eqA 4060 (compA 4060 tmTB ruA0A) (compA 4060 ruA0A tmTB) = true := by
    rw [tB_eq, a0_c, compA_u cB cA0, compA_u cA0 cB, eqA_u (cpc cB cA0) (cpc cA0 cB)]
    exact h2
  have p1 : eqA 4060 (powA 4060 tmTA 5) (idA 4060) = true := by
    rw [tA_eq, (powA_u cA 5).1, hidA, eqA_u (powA_u cA 5).2 cE]
    exact h3
  have n1 : eqA 4060 tmTA (idA 4060) = false := by
    rw [tA_eq, hidA, eqA_u cA cE]
    exact notB_beq h4
  have p2 : eqA 4060 (powA 4060 tmTB 7) (idA 4060) = true := by
    rw [tB_eq, (powA_u cB 7).1, hidA, eqA_u (powA_u cB 7).2 cE]
    exact h5
  have n2 : eqA 4060 tmTB (idA 4060) = false := by
    rw [tB_eq, hidA, eqA_u cB cE]
    exact notB_beq h6
  have p3 : eqA 4060 (powA 4060 (compA 4060 tmTA tmTB) 13) (idA 4060) = true := by
    rw [tA_eq, tB_eq, compA_u cA cB, (powA_u (cpc cA cB) 13).1, hidA,
      eqA_u (powA_u (cpc cA cB) 13).2 cE]
    exact h7
  have n3 : eqA 4060 (compA 4060 tmTA tmTB) (idA 4060) = false := by
    rw [tA_eq, tB_eq, compA_u cA cB, hidA, eqA_u (cpc cA cB) cE]
    exact notB_beq h8
  unfold tmABCheck
  simp only [iA.2, iB.2, m1, m2, p1, n1, p2, n2, p3, n3, Bool.true_and, Bool.not_false]

theorem zl : tmZLCheck = true := by
  have cA0 := gens_c.1
  obtain ⟨cL, cLI, pL⟩ := inv_parts.2.2.1
  obtain ⟨-, -, pAl⟩ := inv_parts.2.2.2.1
  obtain ⟨-, -, pBl⟩ := inv_parts.2.2.2.2.1
  have cZ := inv_parts.2.2.2.2.2.1
  have h := kZL
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h
  have z1 : eqA 4060 (compA 4060 tmTZ tmTZ) (idA 4060) = true := by
    rw [tZ_eq, compA_u cZ cZ, hidA, eqA_u (cpc cZ cZ) cE]
    exact h1
  have z2 : eqA 4060 tmTZ (idA 4060) = false := by
    rw [tZ_eq, hidA, eqA_u cZ cE]
    exact notB_beq h2
  have z3 : (tmTZ[tmZFix]! == tmZFix) = true := by
    have e0 : tmZFix = 0 := rfl
    have hz0 := Nat.eq_of_beq_eq_true h3
    rw [e0, tZ_eq, CFSG.KC.BfsPin.unpack_get' (by norm_num), hz0]
    rfl
  have iL := inv_u tL_eq pL
  have iAl := inv_u tAl_eq pAl
  have iBl := inv_u tBl_eq pBl
  have z4 : eqA 4060 (compA 4060 (compA 4060 tmTL ruA0A) (ruInv tmTL)) (compA 4060 ruA0A tmTZ) =
      true := by
    rw [tLi_eq, tL_eq, a0_c, tZ_eq, compA_u cL cA0, compA_u (cpc cL cA0) cLI, compA_u cA0 cZ,
      eqA_u (cpc (cpc cL cA0) cLI) (cpc cA0 cZ)]
    exact h4
  unfold tmZLCheck
  simp only [z1, z2, z3, iL.2, iAl.2, iBl.2, z4, Bool.true_and, Bool.and_true, Bool.not_false]
  decide

theorem gen : tmGenCheck = true := by
  have h := kGen
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  have cA0 := gens_c.1
  have cA1 := gens_c.2.1
  unfold tmGenCheck
  rw [gen4i_eq, word_of gen4_bind gen4_p letters.2.2.2.2.1,
    word_of gen4_bind gen4_p letters.2.2.2.2.2.1, Nat.eq_of_beq_eq_true h1,
    Nat.eq_of_beq_eq_true h2, a0_c, a1_c, eqA_u cA0 cA0, eqA_u cA1 cA1, Nat.beq_refl,
    Nat.beq_refl]
  rfl

theorem sTabs_get {i : Nat} (hi : i < 4) : tmSTabs[i]! = unpack 4060 12 (SG i) := by
  rw [← sG_eq hi]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem sTabs_size : tmSTabs.size = 4 := rfl

theorem enum_parts : SE.cnt = 64 ∧ SE.k = 4 ∧ penumHdK e SE.cnt 64 SE.T SE.PL = true ∧
    (∀ i < 4, SE.G i = SG i) ∧
    penumSlK 4060 12 (mask 12) (4060 * 12) false SE.G SE.GI 4 SE.cnt SE.T SE.PL SE.POS SE.SRT
      SE.SRI 0 64 = true := by
  have h := kEnum
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h5⟩ := andB_iff.1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3,
    fun i hi => Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 h4 i hi), h5⟩

theorem gensS : GensOK 4060 12 4 SE.G tmSTabs := by
  refine ⟨sTabs_size, fun j hj => ?_⟩
  rw [enum_parts.2.2.2.1 j hj, sTabs_get hj]
  exact ⟨rfl, (inv_parts.2.2.2.2.2.2.1 j hj).1⟩

theorem ptS : ∀ i < SE.cnt, penumPtK 4060 12 (mask 12) (4060 * 12) false SE.G SE.GI 4 SE.cnt SE.T
    SE.PL SE.POS SE.SRT SE.SRI i = true := fun i hi =>
  penumSl_spec enum_parts.2.2.2.2 i (Nat.zero_le _) (by rw [enum_parts.1] at hi; omega) hi

theorem encS : enumBFS 4060 tmSTabs 64 = penumRec 4060 12 SE.cnt SE.T SE.PL ∧
    enumOK 4060 tmSTabs (penumRec 4060 12 SE.cnt SE.T SE.PL) = true :=
  penumK_left_sound hsz gensS enum_parts.2.2.1 ptS

theorem zj_eq {j : Nat} (hj : j < 7) : tmZj j = unpack 4060 12 (ZJ j) ∧ Cn (ZJ j) := by
  obtain ⟨cC, cCI, pC⟩ := inv_parts.2.2.2.2.2.2.2 j hj
  have cZ := inv_parts.2.2.2.2.2.1
  have iC := inv_u (cG_eq hj) pC
  unfold tmZj ZJ
  rw [iC.1, cG_eq hj, tZ_eq]
  unfold conjTab
  rw [comp_u cC cZ, comp_u (cpc cC cZ) cCI]
  exact ⟨rfl, cpc (cpc cC cZ) cCI⟩

theorem cover_pt {x : Nat} (hx : Cn x) (h : orB (Nat.beq x e) (orB (notB (invPt 4060 12 x))
    (orB (notB (allN 4 fun g => commPt 4060 12 x (SG g)))
      (notB (allN 7 fun j => notB (Nat.beq x (ZJ j)))))) = true) :
    (unpack 4060 12 x == idTab 4060 || !(comp 4060 (unpack 4060 12 x) (unpack 4060 12 x) == idTab 4060) ||
      !(tmSTabs.all fun g => comp 4060 (unpack 4060 12 x) g == comp 4060 g (unpack 4060 12 x)) ||
      (List.range 7).any fun j => unpack 4060 12 x == tmZj j) = true := by
  have e1 : (unpack 4060 12 x == idTab 4060) = Nat.beq x e := by rw [hidT, beq_u hx cE]
  have e2 : (comp 4060 (unpack 4060 12 x) (unpack 4060 12 x) == idTab 4060) = invPt 4060 12 x := by
    rw [Bool.eq_iff_iff, beq_iff_eq, invPt_iff hx]
  have e3 : (tmSTabs.all fun g => comp 4060 (unpack 4060 12 x) g == comp 4060 g (unpack 4060 12 x)) =
      allN 4 fun g => commPt 4060 12 x (SG g) := by
    rw [Bool.eq_iff_iff, Array.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
    constructor
    · intro H g hg
      have H' := H g (by rw [sTabs_size]; exact hg)
      rw [← getElem!_pos tmSTabs g (by rw [sTabs_size]; exact hg), sTabs_get hg, beq_iff_eq] at H'
      exact (commPt_iff hx (inv_parts.2.2.2.2.2.2.1 g hg).1).2 H'
    · intro H g hg
      have hg' : g < 4 := by rw [sTabs_size] at hg; exact hg
      rw [← getElem!_pos tmSTabs g hg, sTabs_get hg', beq_iff_eq]
      exact (commPt_iff hx (inv_parts.2.2.2.2.2.2.1 g hg').1).1 (H g hg')
  have e4 : ((List.range 7).any fun j => unpack 4060 12 x == tmZj j) =
      !(allN 7 fun j => notB (Nat.beq x (ZJ j))) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
      CFSG.KS.Raw.Orb.allN_iff]
    constructor
    · rintro ⟨j, hj, hq⟩ H
      have hj' := List.mem_range.1 hj
      rw [(zj_eq hj').1, beq_u hx (zj_eq hj').2] at hq
      have := H j hj'
      rw [hq] at this
      exact Bool.noConfusion this
    · intro H
      by_contra hn
      apply H
      intro j hj
      have : (unpack 4060 12 x == tmZj j) = false := by
        cases hb : (unpack 4060 12 x == tmZj j)
        · rfl
        · exact absurd ⟨j, List.mem_range.2 hj, hb⟩ hn
      rw [(zj_eq hj).1, beq_u hx (zj_eq hj).2] at this
      rw [this]
      rfl
  rw [e1, e2, e3, e4]
  rcases orB_iff.1 h with h1 | h1
  · rw [h1]; rfl
  rcases orB_iff.1 h1 with h2 | h2
  · rw [notB_iff] at h2
    rw [h2]
    simp
  rcases orB_iff.1 h2 with h3 | h3
  · rw [notB_iff] at h3
    rw [h3]
    simp
  · rw [notB_iff] at h3
    rw [h3]
    simp

theorem sylow : tmSylowCheck = true := by
  have cZ := inv_parts.2.2.2.2.2.1
  have hs : (List.range 4).all (fun i => isInvA 4060 (tmSGen i) (ruInv (tmSGen i))) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    exact (inv_u (sG_eq hi') (inv_parts.2.2.2.2.2.2.1 i hi').2.2).2
  have hc : (List.range 7).all (fun j => isInvA 4060 (tmCGen j) (ruInv (tmCGen j))) = true := by
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    exact (inv_u (cG_eq hj') (inv_parts.2.2.2.2.2.2.2 j hj').2.2).2
  have hz : tmSTabs.all (fun g => comp 4060 g tmTZ == comp 4060 tmTZ g) = true := by
    rw [Array.all_eq_true]
    intro g hg
    have hg' : g < 4 := by rw [sTabs_size] at hg; exact hg
    have cS := (inv_parts.2.2.2.2.2.2.1 g hg').1
    rw [← getElem!_pos tmSTabs g hg, sTabs_get hg', tZ_eq, comp_u cS cZ, comp_u cZ cS,
      beq_u (cpc cS cZ) (cpc cZ cS)]
    exact CFSG.KS.Raw.Orb.allN_iff.1 kSyl g hg'
  have hE : tmSEnum = penumRec 4060 12 SE.cnt SE.T SE.PL := by
    unfold tmSEnum
    exact encS.1
  have hsize : tmSEnum.tabs.size = 64 := by
    rw [hE, penumRec_eq, Array.size_ofFn, enum_parts.1]
  have hcov : tmCentralCover tmSEnum = true := by
    unfold tmCentralCover
    rw [hE, penumRec_eq, Array.all_eq_true]
    intro i hi
    have hi' : i < SE.cnt := by simpa using hi
    rw [Array.getElem_ofFn]
    have h := CFSG.KS.Raw.Orb.allN_iff.1 kCover i (by rw [enum_parts.1] at hi'; exact hi')
    rw [strictB_app] at h
    exact cover_pt (penumPt_canon (ptS i hi')) h
  unfold tmSylowCheck
  rw [hs, hc, hz, hE, encS.2, ← hE, hsize, hcov]
  rfl

theorem check27100 : tmRuCheck = true := by
  unfold tmRuCheck
  rw [basic, ab, zl, gen, sylow]
  rfl

end CertificateChecks.KernelSporSch.TMem27100

end
