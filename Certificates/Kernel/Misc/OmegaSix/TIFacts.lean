module

public import Certificates.Kernel.Misc.OmegaSix.TIChecks
public import Certificates.Kernel.Misc.OmegaSix.FinalO
public import CFSG.Certificates.Kernel.Misc.OmegaSixTISound
public import Certificates.Data.Foote82OmegaSixTI

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.InvolA6 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.KC.OmegaSix CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KC.YamakiRepF
  CFSG.CGT.Foote82.CaseIIClassAux
open CFSG.KD.Sp62 (MULF ONE)

theorem tiRec : ∀ t < 51840, tiAt RO (recX ROO 3 t) (TIW t) = true := by
  have hc : ∀ q < 102, tiChunk RO ROO TIW 512 q = true := fun q hq => ch919010K.all q hq
  have hall := CFSG.KC.Misc.Clos.forall_of_chunks 512 102
    (fun t => bIf(Nat.blt t 51840, strictY (recX ROO 3 t) fun X => tiAt RO X (TIW t), true)) hc
  intro t ht
  have h := hall t (by omega)
  rw [Nat.blt_eq.mpr ht, strictY_eq] at h
  exact h

theorem wit_any {X w : ℕ} (h : tiWitK RO X w = true) :
    anyLt (bfsEnum (genA6 ()) 25920).elems.size (fun j =>
      decide (((bfsEnum (genA6 ()) 25920).lookup (invArr (bfsEnum (genA6 ()) 25920).elems[j]!)).getD 0 <
        (bfsEnum (genA6 ()) 25920).elems.size) &&
      compA (bfsEnum (genA6 ()) 25920).elems[j]! (bfsEnum (genA6 ()) 25920).elems[
        ((bfsEnum (genA6 ()) 25920).lookup (invArr (bfsEnum (genA6 ()) 25920).elems[j]!)).getD 0]! ==
        idA () &&
      tiWitness (arrF X) (bfsEnum (genA6 ()) 25920).elems[j]! (bfsEnum (genA6 ()) 25920).elems[
        ((bfsEnum (genA6 ()) 25920).lookup (invArr (bfsEnum (genA6 ()) 25920).elems[j]!)).getD 0]!) =
      true := by
  have T := omega_inv oMatA oMatB oHead oTab
  unfold tiWitK at h
  simp only [strictY_eq] at h
  generalize Nat.land w 32767 = j at h
  generalize Nat.land (Nat.shiftRight w 15) 32767 = k at h
  generalize Nat.shiftRight w 30 = c at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hj, hk⟩, hc⟩, h1⟩, h2⟩, hP⟩, hs⟩ := h
  have hsz := T.1.1
  have hel : ∀ t < 25920, (bfsEnum (genA6 ()) 25920).elems[t]! = arrF (recX RO 10 t) :=
    T.1.2.2.2.1
  refine anyLt_of (j := j) (by rw [hsz]; exact hj) ?_
  have hinv : invArr (bfsEnum (genA6 ()) 25920).elems[j]! = arrF (recX RO 10 k) := by
    rw [hel j hj]
    exact invArr_arrF h1 h2
  have hl : (bfsEnum (genA6 ()) 25920).lookup (arrF (recX RO 10 k)) = some k := by
    have := lookup_of_BInvE T.1 hk
    simpa using this
  rw [hinv, hl, Option.getD_some, hel j hj, hel k hk, hsz]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hk, ?_⟩, ?_⟩
  · rw [arrF_mul, h1, arrF_one]
    exact beq_self_eq_true _
  · unfold tiWitness
    simp only []
    rw [arrF_mul, arrF_mul, arrF_mul, arrF_mul, hP, arrF_one, beq_self_eq_true, Bool.true_and,
      List.any_eq_true]
    have hc' : 2 ^ c < 64 :=
      calc 2 ^ c < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hc
        _ = 64 := by norm_num
    refine ⟨2 ^ c, List.mem_range.2 hc', ?_⟩
    have e : (arrF (MULF (MULF (recX RO 10 j) X) (recX RO 10 k)))[2 ^ c]! ^^^ 2 ^ c =
        subK (MULF (MULF (recX RO 10 j) X) (recX RO 10 k)) c := by
      rw [← subOne_eq _ c hc]
      rfl
    have hw : subK (MULF (MULF (recX RO 10 j) X) (recX RO 10 k)) c < 64 := by
      rw [← subOne_eq _ c hc]
      exact subOne_lt _ hc'
    rw [e, bne_iff_ne]
    intro e2
    have hz : sK X (subK (MULF (MULF (recX RO 10 j) X) (recX RO 10 k)) c) = 0 := by
      rw [← sK_eq X hw, subOneCode, e2, Nat.xor_self]
    rw [hz] at hs
    exact absurd hs (by decide)

theorem tiCheck_ok : tiCheck () = true := by
  have TO := oEnum_inv (L := 256) (m := 203) oMatAO oMatBO oMatRO (by norm_num) oHeadO oTabO
  unfold tiCheck oEnum omegaEnum
  simp only []
  rw [allLt_iff]
  intro i hi
  rw [TO.1.1] at hi
  have hX := TO.2 i hi
  have he : (bfsEnum (genO ()) 51840).elems[i]! = arrF (recX ROO 3 i) := TO.1.2.2.2.1 i hi
  rw [he]
  have h := tiRec i hi
  generalize recX ROO 3 i = X at h hX ⊢
  generalize TIW i = w at h
  unfold tiAt at h
  simp only [Bool.or_eq_true]
  cases hXX : Nat.beq (MULF X X) ONE
  · left; left; left
    rw [arrF_mul, ← arrF_one, bne, beq_arrF (CFSG.KC.Sp62.MULF_lt _ _) CFSG.KC.YamakiS0.ONE_lt, hXX]
    rfl
  rw [hXX] at h
  cases hX1 : Nat.beq X ONE
  · rw [hX1] at h
    cases hr : rank1K X
    · rw [hr] at h
      right
      exact wit_any h
    · left; right
      exact rank1_of hr
  · left; left; right
    rw [← arrF_one, beq_arrF hX CFSG.KC.YamakiS0.ONE_lt, hX1]

end CFSG.KD.OmegaSix

end
