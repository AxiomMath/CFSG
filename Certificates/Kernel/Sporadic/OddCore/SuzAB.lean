module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.SuzRecog.TwistTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzAB

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native

meta def mM : Array (Array Nat) := matTabs

meta def iM : Array (Array Nat) :=
  #[invTab 64 (comp 64 matTabs[1]! (idTab 64)),
    invTab 64 (comp 64 matTabs[6]! (comp 64 matTabs[4]! (idTab 64)))]

end CertificateChecks.KernelSpor.SuzAB

#kmisc_packarrs CertificateChecks.KernelSpor.SuzABM CertificateChecks.KernelSpor.SuzAB.mM 7
#kmisc_packarrs CertificateChecks.KernelSpor.SuzABI CertificateChecks.KernelSpor.SuzAB.iM 7

namespace CertificateChecks.KernelSpor.SuzAB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.SuzRecog CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.SuzB0

local notation "pc" => pcomp 64 7 (mask 7)
local notation "cn" => canonK 64 7 (mask 7) (64 * 7)
local notation "Id" => pidn 64 7

@[expose] noncomputable def AK : Nat := pc (SuzABM 1) Id

@[expose] noncomputable def BK : Nat := pc (SuzABM 6) (pc (SuzABM 4) Id)

@[expose] noncomputable def letK (l : Fin 2 × Bool) : Nat :=
  if l.1 = 0 then (if l.2 then AK else SuzABI 0) else (if l.2 then BK else SuzABI 1)

@[expose] noncomputable def wordK (v : List (Fin 2 × Bool)) : Nat :=
  v.foldr (fun l t => pc (letK l) t) Id

theorem kBind : (Nat.beq matTabs.size 10 && allN 10 fun k => bindArrK matTabs[k]! 64 7 (SuzABM k)) =
    true := by
  quickRfl

theorem kCan : (allN 10 (fun k => cn (SuzABM k)) && cn (SuzABI 0) && cn (SuzABI 1) && cn Id &&
    idK 64 7 (mask 7)) = true := by
  quickRfl

theorem kInv : (invEqK 64 7 (mask 7) (64 * 7) AK (SuzABI 0) &&
    invEqK 64 7 (mask 7) (64 * 7) BK (SuzABI 1)) = true := by
  quickRfl


theorem negInv : Bool.not (invEqK 64 7 (mask 7) (64 * 7) AK (Nat.xor (SuzABI 0) 1)) = true := by
  quickRfl

theorem negGen : Bool.not (allBelow 10 fun k =>
    Nat.beq (wordK ((genWords.getD k []).map fun l => (0, l.2))) (SuzABM k)) = true := by
  quickRfl

@[expose] def P (a : Array Nat) (A : Nat) : Prop := a = unpack 64 7 A ∧ cn A = true

theorem facts : (∀ k < 10, matTabs[k]! = unpack 64 7 (SuzABM k)) ∧ (∀ k < 10, cn (SuzABM k) = true) ∧
    cn (SuzABI 0) = true ∧ cn (SuzABI 1) = true ∧ cn Id = true ∧
    unpack 64 7 Id = CFSG.Monster.B.Co2.Native.idA 64 := by
  have hb := (binds_of_check kBind).2
  have h := kCan
  simp only [Bool.and_eq_true] at h
  exact ⟨hb, allN_spec h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, idK_sound h.2⟩

theorem p_comp {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    P (comp 64 a b) (pc A B) := by
  rw [ha.1, hb.1]
  exact ⟨compA_unpack ha.2 hb.2, canonK_pcomp ha.2 hb.2⟩

theorem pId : P (idTab 64) Id := ⟨facts.2.2.2.2.2.symm, facts.2.2.2.2.1⟩

theorem pM {k : Nat} (hk : k < 10) : P matTabs[k]! (SuzABM k) := ⟨facts.1 k hk, facts.2.1 k hk⟩

theorem pA : P aTab AK := p_comp (pM (by norm_num)) pId

theorem pB : P bTab BK := p_comp (pM (by norm_num)) (p_comp (pM (by norm_num)) pId)

theorem pAI : P aInv (SuzABI 0) := by
  have e : aInv = CFSG.Monster.B.Co2.Native.invCand 64 aTab := rfl
  have h := kInv
  rw [Bool.and_eq_true] at h
  rw [e, pA.1]
  exact ⟨(invEqK_sound h.1).1, facts.2.2.1⟩

theorem pBI : P bInv (SuzABI 1) := by
  have e : bInv = CFSG.Monster.B.Co2.Native.invCand 64 bTab := rfl
  have h := kInv
  rw [Bool.and_eq_true] at h
  rw [e, pB.1]
  exact ⟨(invEqK_sound h.2).1, facts.2.2.2.1⟩

theorem pL (l : Fin 2 × Bool) : P (letterTab64 l) (letK l) := by
  unfold letterTab64 letK
  split_ifs
  exacts [pA, pAI, pB, pBI]

theorem word_P (v : List (Fin 2 × Bool)) : P (wordTab64 v) (wordK v) := by
  unfold wordTab64 wordK
  induction v with
  | nil => exact pId
  | cons l v ih =>
    rw [List.foldr_cons, List.foldr_cons]
    exact p_comp (pL l) ih

theorem beq_P {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    (a == b) = Nat.beq A B := by
  rw [ha.1, hb.1]
  exact CFSG.KS.PEnum.beq_unpack ha.2 hb.2

theorem size_P {a : Array Nat} {A : Nat} (ha : P a A) : a.size = 64 := by
  rw [ha.1]
  simp [unpack]

theorem all_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ k ∈ l, p k = q k) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun k hk => h k (List.mem_cons_of_mem _ hk)]

theorem abCheck_true : abCheck = true := by
  have hf : (fun r => wordTab64 r == idTab 64) = (fun r => Nat.beq (wordK r) Id) :=
    funext fun r => beq_P (word_P r) pId
  have hg : allBelow 10 (fun k => wordTab64 (genWords.getD k []) == matTabs[k]!) =
      allBelow 10 (fun k => Nat.beq (wordK (genWords.getD k [])) (SuzABM k)) :=
    all_congr' fun k hk => beq_P (word_P _) (pM (List.mem_range.1 hk))
  unfold abCheck
  rw [size_P pAI, size_P pBI, beq_P (p_comp pAI pA) pId, beq_P (p_comp pBI pB) pId, hf,
    beq_P (word_P _) pId, beq_P (word_P _) pId, hg]
  quickRfl

end CertificateChecks.KernelSpor.SuzAB

end
