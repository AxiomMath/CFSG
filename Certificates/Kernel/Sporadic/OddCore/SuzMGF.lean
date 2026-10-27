module

public import Certificates.Kernel.Sporadic.OddCore.SuzMG
public import Certificates.Kernel.Sporadic.OddCore.SuzTwCF
public import Certificates.Kernel.LocalComp.B0SuzData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzMGF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.ModelGroupsData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11

@[expose] noncomputable def W1K : Nat := pc (SuzTwG 2) (pc (SuzTwG 6) (SuzTwGI 2))

@[expose] noncomputable def W2K : Nat := pc (SuzTwG 6) W1K

@[expose] noncomputable def R0K (r : Nat) : Nat :=
  if r = 0 then Id else if r = 1 then SuzTwG 6 else if r = 2 then W1K else W2K

@[expose] noncomputable def powK (X : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Id (fun _ ih => pc X ih) k

@[expose] noncomputable def a4K (i : Nat) : Nat := pc (R0K (i / 3)) (powK (SuzTwG 2) (i % 3))

@[expose] noncomputable def e8K (i : Nat) : Nat := pc (R0K (i / 2)) (powK (SuzMGG 4) (i % 2))

@[expose] noncomputable def conjK (g gi x : Nat) : Nat := pc g (pc x gi)

@[expose] noncomputable def cWK (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) Id (fun k _ ih => pc (SuzInvT1.F (18 + k)) ih) w

@[expose] noncomputable def tauK : Nat :=
  pc (cWK [5, 8, 6, 7, 4]) (pc (pc (pc (pc Id (KernelLC.SuzB0Q.F 0)) (KernelLC.SuzB0Q.F 1))
    (KernelLC.SuzB0Q.F 2)) (KernelLC.SuzB0Q.F 4))

@[expose] noncomputable def inZK (R X : Nat) : Bool := Nat.beq X R || Nat.beq X (pc R R)

@[expose] noncomputable def inR0K (X : Nat) : Bool :=
  Nat.beq X (SuzTwG 6) || Nat.beq X W1K || Nat.beq X W2K

@[expose] noncomputable def pairK (g gi : Nat) : Bool :=
  (inZK (SuzTwG 2) (conjK g gi (SuzTwG 2)) && inZK (SuzMGG 5) (conjK g gi (SuzMGG 5))) ||
    (inZK (SuzMGG 5) (conjK g gi (SuzTwG 2)) && inZK (SuzTwG 2) (conjK g gi (SuzMGG 5)))

@[expose] noncomputable def idxK (X : Nat) : Nat :=
  ((List.range 12).find? fun j => Nat.beq X (SuzMGA j)).getD 12

theorem kBind : (Nat.beq (SuzMGG 0) (SuzMGC1S.F 0) && Nat.beq (SuzMGG 1) (SuzMGC1S.F 1) &&
    Nat.beq (SuzMGG 2) (SuzMGS1.F 0) && Nat.beq (SuzMGG 3) (SuzMGS2.F 0) &&
    Nat.beq (SuzMGG 4) tauK && Nat.beq (SuzMGG 5) (conjK (SuzTwG 6) (SuzTwGI 6) (SuzTwG 2))) =
    true := by
  quickRfl

theorem kCan : (allN 6 (fun i => cn (SuzMGG i) && cn (SuzMGGI i)) &&
    allN 12 (fun i => cn (SuzMGAI i)) && allN 8 (fun i => cn (SuzMGEI i)) &&
    allN 10 (fun k => cn (SuzInvT1.F (18 + k))) && allN 6 (fun i => cn (KernelLC.SuzB0Q.F i))) =
    true := by
  quickRfl

theorem kInv : (allN 6 (fun i => ie (SuzMGG i) (SuzMGGI i)) &&
    allN 12 (fun i => ie (SuzMGA i) (SuzMGAI i)) && allN 8 (fun i => ie (SuzMGE i) (SuzMGEI i))) =
    true := by
  quickRfl

theorem kPinA : allN 12 (fun i => Nat.beq (SuzMGA i) (a4K i) &&
    Nat.beq (SuzMGC (2 * i)) (conjK (SuzMGA i) (SuzMGAI i) (SuzTwG 2)) &&
    Nat.beq (SuzMGC (2 * i + 1)) (conjK (SuzMGA i) (SuzMGAI i) (SuzMGG 5))) = true := by
  quickRfl

theorem kPinE : allN 8 (fun i => Nat.beq (SuzMGE i) (e8K i) &&
    Nat.beq (SuzMGEC i) (conjK (SuzMGE i) (SuzMGEI i) (SuzTwG 2))) = true := by
  quickRfl

theorem kMem : (msift (SuzTwG 2) && msift (SuzTwG 6) && msift (SuzTP 1) && msift (SuzMGG 0) &&
    msift (SuzMGG 1) && msift (SuzMGG 2) && msift (SuzMGG 3)) = true := by
  quickRfl

theorem kComm : (Nat.beq (pc (SuzTP 1) (SuzTwG 2)) (pc (SuzTwG 2) (SuzTP 1)) &&
    Nat.beq (pc (SuzMGG 0) (SuzTwG 2)) (pc (SuzTwG 2) (SuzMGG 0)) &&
    Nat.beq (pc (SuzMGG 0) (SuzTP 1)) (pc (SuzTP 1) (SuzMGG 0)) &&
    Nat.beq (pc (SuzMGG 1) (SuzTP 1)) (pc (SuzTP 1) (SuzMGG 1)) &&
    Nat.beq (pc (SuzMGG 2) (SuzTP 1)) (pc (SuzTP 1) (SuzMGG 2)) &&
    Nat.beq (pc (SuzMGG 3) (SuzTP 1)) (pc (SuzTP 1) (SuzMGG 3))) = true := by
  quickRfl

theorem kBasic : (Nat.beq (powK (SuzTwG 2) 3) Id && !Nat.beq (SuzTwG 2) Id &&
    Nat.beq (pc (SuzTwG 2) (SuzMGGI 5)) W2K && !inZK (SuzMGG 5) (SuzTwG 2)) = true := by
  quickRfl

theorem kNorm : (inR0K (conjK (SuzMGG 3) (SuzMGGI 3) (SuzTwG 6)) &&
    inR0K (conjK (SuzMGG 3) (SuzMGGI 3) W1K)) = true := by
  quickRfl

theorem kPair : (pairK (SuzMGG 4) (SuzMGGI 4) && pairK (SuzMGG 1) (SuzMGGI 1) &&
    pairK (SuzMGG 3) (SuzMGGI 3)) = true := by
  quickRfl

theorem kA4 : allN 12 (fun i =>
    decide (idxK (pc (SuzTwG 2) (SuzMGA i)) < 12) &&
    Nat.beq (pc (SuzTwG 2) (SuzMGA i)) (a4K (idxK (pc (SuzTwG 2) (SuzMGA i)))) &&
    decide (idxK (pc (SuzMGG 5) (SuzMGA i)) < 12) &&
    Nat.beq (pc (SuzMGG 5) (SuzMGA i)) (a4K (idxK (pc (SuzMGG 5) (SuzMGA i)))) &&
    (i % 3 == 0 || !Nat.beq (pc (SuzMGA i) (SuzMGA i)) Id)) = true := by
  quickRfl

theorem kA4P : allN 12 (fun i => allN 12 fun j => i == j ||
    !inZK (SuzMGC (2 * i)) (SuzMGC (2 * j)) ||
    !inZK (SuzMGC (2 * i + 1)) (SuzMGC (2 * j + 1))) = true := by
  quickRfl

theorem kE8 : allN 8 (fun i => allN 8 fun j => i == j || !Nat.beq (SuzMGEC i) (SuzMGEC j)) =
    true := by
  quickRfl

theorem negA : Bool.not (allN 12 (fun i => Nat.beq (Nat.xor (SuzMGA i) 1) (a4K i))) = true := by
  quickRfl

theorem negE8 : Bool.not (allN 8 (fun i => allN 8 fun j => i == j ||
    !Nat.beq (SuzMGEC (i % 7)) (SuzMGEC (j % 7)))) = true := by
  quickRfl

theorem allLt_of {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allLt n f = true := by
  unfold allLt
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

theorem find_congr {l : List Nat} {p q : Nat → Bool} (h : ∀ j ∈ l, p j = q j) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem p_invR {a : Array Nat} {A AI : Nat} (ha : P a A) (hi : ie A AI = true)
    (hc : cn AI = true) : P (invCand 1782 a) AI ∧ isInvA 1782 a (invCand 1782 a) = true := by
  have h := invEqK_sound hi
  rw [ha.1, h.1]
  exact ⟨⟨rfl, hc⟩, h.2⟩

theorem p_conjR {g a : Array Nat} {G GI A : Nat} (hg : P g G) (hgi : P (invCand 1782 g) GI)
    (ha : P a A) : P (conjA g a) (conjK G GI A) := by
  unfold conjA conjK
  exact p_comp hg (p_comp ha hgi)

theorem p_eq {a : Array Nat} {A B : Nat} (ha : P a A) (h : Nat.beq B A = true) : P a B := by
  rw [Nat.eq_of_beq_eq_true h]
  exact ha

theorem p_pow {a : Array Nat} {A : Nat} (ha : P a A) :
    ∀ k, P (CFSG.Sporadic.SuzOddCore.powA 1782 a k) (powK A k)
  | 0 => pidn_P
  | k + 1 => by
    rw [CFSG.Sporadic.SuzOddCore.powA]
    exact p_comp ha (p_pow ha k)

theorem bind : Nat.beq (SuzMGG 0) (SuzMGC1S.F 0) = true ∧ Nat.beq (SuzMGG 1) (SuzMGC1S.F 1) = true ∧
    Nat.beq (SuzMGG 2) (SuzMGS1.F 0) = true ∧ Nat.beq (SuzMGG 3) (SuzMGS2.F 0) = true ∧
    Nat.beq (SuzMGG 4) tauK = true ∧
    Nat.beq (SuzMGG 5) (conjK (SuzTwG 6) (SuzTwGI 6) (SuzTwG 2)) = true := by
  have h := kBind
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem can : (∀ i < 6, cn (SuzMGG i) = true ∧ cn (SuzMGGI i) = true) ∧
    (∀ i < 12, cn (SuzMGAI i) = true) ∧ (∀ i < 8, cn (SuzMGEI i) = true) ∧
    (∀ k < 10, cn (SuzInvT1.F (18 + k)) = true) ∧ (∀ i < 6, cn (KernelLC.SuzB0Q.F i) = true) := by
  have h := kCan
  simp only [Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, allN_spec h.1.1.1.2, allN_spec h.1.1.2, allN_spec h.1.2,
    allN_spec h.2⟩
  have := allN_spec h.1.1.1.1 i hi
  rw [Bool.and_eq_true] at this
  exact this

theorem inv : (∀ i < 6, ie (SuzMGG i) (SuzMGGI i) = true) ∧
    (∀ i < 12, ie (SuzMGA i) (SuzMGAI i) = true) ∧ (∀ i < 8, ie (SuzMGE i) (SuzMGEI i) = true) := by
  have h := kInv
  simp only [Bool.and_eq_true] at h
  exact ⟨allN_spec h.1.1, allN_spec h.1.2, allN_spec h.2⟩

theorem hexJ_eq {cs : List Char} {s : String} {F : Nat → Nat} {N : Nat} (hs : s = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 1782 11 N F = true) {j : Nat} (hj : j < N) :
    hexTable 3 1782 (1782 * j) s = unpack 1782 11 (F j) := by
  rw [hs]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound h j hj

theorem pG_of {a : Array Nat} {i : Nat} (hi : i < 6) {F : Nat} (hF : Nat.beq (SuzMGG i) F = true)
    (ha : a = unpack 1782 11 F) : P a (SuzMGG i) := by
  rw [ha, ← Nat.eq_of_beq_eq_true hF]
  exact ⟨rfl, (can.1 i hi).1⟩

theorem pAa : P aA (SuzMGG 0) := by
  refine pG_of (by norm_num) bind.1 ?_
  unfold aA c1Strong
  exact hexJ_eq SuzMGC1S.eq SuzMGC1S.all (j := 0) (by norm_num)

theorem pBb : P bA (SuzMGG 1) := by
  refine pG_of (by norm_num) bind.2.1 ?_
  unfold bA c1Strong
  exact hexJ_eq SuzMGC1S.eq SuzMGC1S.all (j := 1) (by norm_num)

theorem pS1 : P s1Arr (SuzMGG 2) := pG_of (by norm_num) bind.2.2.1 (hex_eq SuzMGS1.eq SuzMGS1.all)

theorem pS2 : P s2Arr (SuzMGG 3) :=
  pG_of (by norm_num) bind.2.2.2.1 (hex_eq SuzMGS2.eq SuzMGS2.all)

theorem c_eq {k : Nat} (hk : k < 10) :
    CFSG.ComponentClassification.AS81.SuzB0.cTab k = unpack 1782 11 (SuzInvT1.F (18 + k)) := by
  have hic : invInnerGenCounts.getD 1 0 = 10 := rfl
  have his : invInnerStart 1 = 18 := rfl
  unfold CFSG.ComponentClassification.AS81.SuzB0.cTab
  rw [getElem!_pos (invInnerGenArrs 1) k (by rw [invInnerGenArrs, Array.size_ofFn, hic]; exact hk)]
  simp only [invInnerGenArrs, Array.getElem_ofFn, his]
  exact SuzInv.run_eq1 (by omega)

theorem pC {k : Nat} (hk : k < 10) :
    P (CFSG.ComponentClassification.AS81.SuzB0.cTab k) (SuzInvT1.F (18 + k)) :=
  ⟨c_eq hk, can.2.2.2.1 k hk⟩

theorem pQ {i : Nat} (hi : i < 6) :
    P (CFSG.ComponentClassification.AS81.SuzB0.qArr i) (KernelLC.SuzB0Q.F i) :=
  ⟨KernelLC.B0Suz.q_eq hi, can.2.2.2.2 i hi⟩

theorem pTauM : P tauA (SuzMGG 4) := by
  refine p_eq ?_ bind.2.2.2.2.1
  have e : tauA = compA 1782 (compA 1782 (CFSG.ComponentClassification.AS81.SuzB0.cTab 5)
      (compA 1782 (CFSG.ComponentClassification.AS81.SuzB0.cTab 8)
      (compA 1782 (CFSG.ComponentClassification.AS81.SuzB0.cTab 6)
      (compA 1782 (CFSG.ComponentClassification.AS81.SuzB0.cTab 7)
      (compA 1782 (CFSG.ComponentClassification.AS81.SuzB0.cTab 4) (idA 1782))))))
      (compA 1782 (compA 1782 (compA 1782 (compA 1782 (idA 1782)
        (CFSG.ComponentClassification.AS81.SuzB0.qArr 0))
        (CFSG.ComponentClassification.AS81.SuzB0.qArr 1))
        (CFSG.ComponentClassification.AS81.SuzB0.qArr 2))
        (CFSG.ComponentClassification.AS81.SuzB0.qArr 4)) := by
    unfold tauA CFSG.Sporadic.SuzRecog.C1Model.tauT CFSG.ComponentClassification.AS81.SuzB0.qProds
    rw [getElem!_pos _ 23 (by simp), Array.getElem_ofFn]
    rfl
  rw [e]
  exact p_comp (p_comp (pC (by norm_num)) (p_comp (pC (by norm_num)) (p_comp (pC (by norm_num))
    (p_comp (pC (by norm_num)) (p_comp (pC (by norm_num)) pidn_P)))))
    (p_comp (p_comp (p_comp (p_comp pidn_P (pQ (by norm_num))) (pQ (by norm_num)))
      (pQ (by norm_num))) (pQ (by norm_num)))

theorem pR2 : P rho2A (SuzMGG 5) := by
  refine p_eq ?_ bind.2.2.2.2.2
  unfold rho2A
  exact p_conjR pW0 (p_inv (by norm_num) pW0.1).1 pRho

theorem pGI_of {a : Array Nat} {i : Nat} (hi : i < 6) (ha : P a (SuzMGG i)) :
    P (invCand 1782 a) (SuzMGGI i) ∧ isInvA 1782 a (invCand 1782 a) = true :=
  p_invR ha (inv.1 i hi) (can.1 i hi).2

theorem pR0 (r : Nat) : P (r0A r) (R0K r) := by
  unfold r0A R0K
  split_ifs
  exacts [pidn_P, pW0, pW1, pW2]

theorem pA4 (i : Nat) : P (a4A i) (a4K i) := by
  unfold a4A a4K
  exact p_comp (pR0 _) (p_pow pRho _)

theorem pE8 (i : Nat) : P (e8A i) (e8K i) := by
  unfold e8A e8K
  exact p_comp (pR0 _) (p_pow pTauM _)

theorem pinA {i : Nat} (hi : i < 12) : Nat.beq (SuzMGA i) (a4K i) = true ∧
    Nat.beq (SuzMGC (2 * i)) (conjK (SuzMGA i) (SuzMGAI i) (SuzTwG 2)) = true ∧
    Nat.beq (SuzMGC (2 * i + 1)) (conjK (SuzMGA i) (SuzMGAI i) (SuzMGG 5)) = true := by
  have h := allN_spec kPinA i hi
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem pinE {i : Nat} (hi : i < 8) : Nat.beq (SuzMGE i) (e8K i) = true ∧
    Nat.beq (SuzMGEC i) (conjK (SuzMGE i) (SuzMGEI i) (SuzTwG 2)) = true := by
  have h := allN_spec kPinE i hi
  rw [Bool.and_eq_true] at h
  exact h

theorem pAi {i : Nat} (hi : i < 12) : P (a4A i) (SuzMGA i) := p_eq (pA4 i) (pinA hi).1

theorem pAI {i : Nat} (hi : i < 12) :
    P (invCand 1782 (a4A i)) (SuzMGAI i) ∧ isInvA 1782 (a4A i) (invCand 1782 (a4A i)) = true :=
  p_invR (pAi hi) (inv.2.1 i hi) (can.2.1 i hi)

theorem pCA {i : Nat} (hi : i < 12) : P (conjA (a4A i) rhoArr) (SuzMGC (2 * i)) :=
  p_eq (p_conjR (pAi hi) (pAI hi).1 pRho) (pinA hi).2.1

theorem pCA2 {i : Nat} (hi : i < 12) : P (conjA (a4A i) rho2A) (SuzMGC (2 * i + 1)) :=
  p_eq (p_conjR (pAi hi) (pAI hi).1 pR2) (pinA hi).2.2

theorem pE {i : Nat} (hi : i < 8) : P (e8A i) (SuzMGE i) := p_eq (pE8 i) (pinE hi).1

theorem pEI {i : Nat} (hi : i < 8) :
    P (invCand 1782 (e8A i)) (SuzMGEI i) ∧ isInvA 1782 (e8A i) (invCand 1782 (e8A i)) = true :=
  p_invR (pE hi) (inv.2.2 i hi) (can.2.2.1 i hi)

theorem pEC {i : Nat} (hi : i < 8) : P (conjA (e8A i) rhoArr) (SuzMGEC i) :=
  p_eq (p_conjR (pE hi) (pEI hi).1 pRho) (pinE hi).2

theorem inZ_P {r x : Array Nat} {R X : Nat} (hr : P r R) (hx : P x X) : inZ r x = inZK R X := by
  unfold inZ inZK
  rw [eqA_P hx hr, eqA_P hx (p_comp hr hr)]

theorem inR0_P {x : Array Nat} {X : Nat} (hx : P x X) : inR0 x = inR0K X := by
  unfold inR0 inR0K
  rw [eqA_P hx pW0, eqA_P hx pW1, eqA_P hx pW2]
  rfl

theorem pairA_P {g : Array Nat} {G GI : Nat} (hg : P g G) (hgi : P (invCand 1782 g) GI) :
    pairA g = pairK G GI := by
  unfold pairA pairK
  rw [inZ_P pRho (p_conjR hg hgi pRho), inZ_P pR2 (p_conjR hg hgi pR2),
    inZ_P pR2 (p_conjR hg hgi pRho), inZ_P pRho (p_conjR hg hgi pR2)]

theorem a4Idx_P {x : Array Nat} {X : Nat} (hx : P x X) : a4Idx x = idxK X := by
  unfold a4Idx idxK
  rw [find_congr fun j hj => eqA_P hx (pAi (List.mem_range.1 hj))]

theorem perms15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permsOK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permsOK
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK
  rw [(p_inv (by norm_num) pRho.1).2, (p_inv (by norm_num) pW0.1).2,
    (pGI_of (by norm_num) pAa).2, (pGI_of (by norm_num) pBb).2, (pGI_of (by norm_num) pS1).2,
    (pGI_of (by norm_num) pS2).2]
  rfl

theorem members15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.membersOK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.membersOK
  rw [inM_eq pRho.1 pRho.2, inM_eq pW0.1 pW0.2, inM_eq pT1.1 pT1.2, inM_eq pAa.1 pAa.2,
    inM_eq pBb.1 pBb.2, inM_eq pS1.1 pS1.2, inM_eq pS2.1 pS2.2]
  exact kMem

theorem comm15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.commOK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.commOK
  rw [commA_P pT1 pRho, commA_P pAa pRho, commA_P pAa pT1, commA_P pBb pT1, commA_P pS1 pT1,
    commA_P pS2 pT1]
  exact kComm

theorem basic15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.basicOK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.basicOK
  rw [eqA_P (p_pow pRho 3) pidn_P, eqA_P pRho pidn_P,
    eqA_P (p_comp pRho (pGI_of (by norm_num) pR2).1) pW2, inZ_P pR2 pRho]
  exact kBasic

theorem norm15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.normOK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.normOK normR0
  have hs := (pGI_of (by norm_num) pS2).1
  rw [inR0_P (p_conjR pS2 hs pW0), inR0_P (p_conjR pS2 hs pW1)]
  exact kNorm

theorem pair15099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.pairOK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.pairOK
  rw [pairA_P pTauM (pGI_of (by norm_num) pTauM).1, pairA_P pBb (pGI_of (by norm_num) pBb).1,
    pairA_P pS2 (pGI_of (by norm_num) pS2).1]
  exact kPair

theorem a415099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.a4OK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.a4OK CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK
  rw [Bool.and_eq_true]
  refine ⟨allLt_of fun i hi => ?_, allLt_of fun i hi => allLt_of fun j hj => ?_⟩
  · have h1 := p_comp pRho (pAi hi)
    have h2 := p_comp pR2 (pAi hi)
    rw [(pAI hi).2, Bool.true_and, a4Idx_P h1, eqA_P h1 (pA4 _), a4Idx_P h2, eqA_P h2 (pA4 _),
      eqA_P (p_comp (pAi hi) (pAi hi)) pidn_P]
    exact allN_spec kA4 i hi
  · rw [inZ_P (pCA hi) (pCA hj), inZ_P (pCA2 hi) (pCA2 hj)]
    exact allN_spec (allN_spec kA4P i hi) j hj

theorem cos815099 : CFSG.Sporadic.SuzRecog.ModelGroupsCheck.cos8OK = true := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.cos8OK
  rw [Bool.and_eq_true]
  refine ⟨allLt_of fun i hi => (pEI hi).2, allLt_of fun i hi => allLt_of fun j hj => ?_⟩
  rw [eqA_P (pEC hi) (pEC hj)]
  exact allN_spec (allN_spec kE8 i hi) j hj

end CertificateChecks.KernelSpor.SuzMGF

end
