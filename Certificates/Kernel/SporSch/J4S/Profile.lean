
module

public import Certificates.Kernel.SporSch.J4S.ProfileK
public import Certificates.Kernel.SporSch.J4S.ProfMath
public import CFSG.Certificates.Kernel.SporSch.J4SProfSound
public import CFSG.Certificates.Kernel.SporSch.J4SSylowSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CertificateChecks.KernelSporSch.J4Profile

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Five

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem PT_get {b j : Nat} (hb : b < 32) (hj : j < 5) : (profTable[b]!)[j]! = ent 24 (J4PT b) j := by
  rw [(bind2_sound J4PT.bind).2 b hb, unpackW_get hj]

theorem hs : ∀ s < 128, Nat.beq (sliceB J4E.T J4SQ.T J4CT.T s) (J4PS s) = true := by
  intro s hs
  have h := allBlk_spec (J4PSC.all s hs) 0 Nat.zero_lt_one
  rwa [show Nat.add (Nat.mul 1 s) 0 = s by simp] at h

theorem prof : (∀ e < 1024, ∀ n < 2048, kfun n e < 5) ∧
    ∀ b < 32, ∀ j < 5, profCount b j = ent 24 (J4PT b) j :=
  prof_sound (fun _ he => E_eq he) SQ_eq (fun e he => lt_of_blt (allN_spec sqb e he))
    CT_eq (fun e he => lt_of_blt (allN_spec ctb e he)) hs tot

theorem dK_sound {a b : Nat} (ha : a < 32) (hb : b < 32) (h : dK a b = true)
    (he : profTable[b]! = profTable[a]!) : b = a := by
  by_contra hne
  unfold dK at h
  rw [show Nat.beq b a = false from Bool.eq_false_iff.2 fun e => hne (Nat.eq_of_beq_eq_true e)] at h
  have hall : allN 5 (fun j => Nat.beq (ent 24 (J4PT b) j) (ent 24 (J4PT a) j)) = true :=
    CFSG.KS.Raw.allN_of_forall fun j hj => by
      rw [← PT_get hb hj, ← PT_get ha hj, he]
      exact Nat.beq_refl _
  rw [hall] at h
  exact Bool.false_ne_true h

theorem facts : (∀ e < 1024, ∀ n < 2048, kfun n e < 5)
    ∧ (∀ b < 32, ∀ j < 5, profCount b j = (profTable[b]!)[j]!)
    ∧ (∀ n < 2048, ell n < 2 ∧ ellV (toVecD 11 n) = (ell n : ZMod 2))
    ∧ (∀ b < 32, ∀ c < 16, ∀ x : ZMod 2,
      (Fin.cons x (toVecD 4 c) : Fin 5 → ZMod 2) = toVecD 5 b ↔
        x = ((b % 2 : ℕ) : ZMod 2) ∧ c = b / 2)
    ∧ (∀ a ∈ [5, 6, 7, 8, 17], ∀ b < 32, profTable[b]! = profTable[a]! → b = a)
    ∧ (profTable.size = 32 ∧ ∀ b < 32, (profTable[b]!).size = 5)
    ∧ (∀ w : Fin 5 → ZMod 2, ∃ b < 32, toVecD 5 b = w)
    ∧ (∀ w : Fin 5 → ZMod 2, ∃ c : Fin 5 → ZMod 2,
      ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = w)
    ∧ (∀ c : Fin 5 → ZMod 2,
      ∑ i, c i • toVecD 5 (![5, 6, 7, 8, 17] i) = 0 → c = 0) := by
  refine ⟨prof.1, fun b hb j hj => by rw [prof.2 b hb j hj, PT_get hb hj],
    J4ProfMath.ellv, J4ProfMath.cons_iff, ?_, ?_, J4ProfMath.surj, J4ProfMath.span,
    J4ProfMath.indep⟩
  · intro a ha b hb he
    have h := allN_spec dist b hb
    obtain ⟨h5, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h6, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h7, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h8, h17⟩ := (bAnd_iff _ _).1 h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact dK_sound (by omega) hb h5 he
    · exact dK_sound (by omega) hb h6 he
    · exact dK_sound (by omega) hb h7 he
    · exact dK_sound (by omega) hb h8 he
    · exact dK_sound (by omega) hb h17 he
  · refine ⟨(bind2_sound J4PT.bind).1, fun b hb => ?_⟩
    rw [(bind2_sound J4PT.bind).2 b hb, unpackW, Array.size_ofFn]

end CertificateChecks.KernelSporSch.J4Profile

end
