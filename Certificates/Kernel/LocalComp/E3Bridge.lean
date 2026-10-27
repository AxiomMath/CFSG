
module

public import Certificates.Kernel.LocalComp.Co3IdentElts
public import CFSG.Certificates.Kernel.E3Sound
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidBase
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidCheckBase
public import Certificates.Data.Kernel.E3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs CFSG.KC.E3
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Co3.Native CertificateChecks.KernelLC CertificateChecks.KernelSpor

theorem zcA_unpack {X : Nat} (hX : Cn X) : zcA (unpack 276 9 X) = zcK P0 P4 EAP X := by
  unfold zcA zcK
  rw [eqA_idA hX, bind4, bind0, ea_eq, eqA_unpack hX c4, eqA_unpack hX c0, eqA_unpack hX cEA]
  cases Nat.beq X (pidn 276 9) <;> cases Nat.beq X P4 <;> cases Nat.beq X P0 <;>
    cases Nat.beq X EAP <;> rfl

theorem powR_canon {t : Nat} (ht : Cn t) : ∀ m, Cn (powR t m)
  | 0 => kCid
  | m + 1 => canon_pc (powR_canon ht m) ht

theorem powA_unpack {t : Nat} (ht : Cn t) : ∀ m, powA (unpack 276 9 t) m = unpack 276 9 (powR t m)
  | 0 => (idK_sound kId).symm
  | m + 1 => by
    unfold powA powR
    rw [powA_unpack ht m, compA_unpack (powR_canon ht m) ht]

theorem profOK_unpack {t : Nat} (ht : Cn t) : ∀ (es : List Nat) {acc : Nat}, Cn acc →
    profOK (unpack 276 9 t) (unpack 276 9 acc) es = profK P0 P4 EAP t acc es
  | [], _, _ => rfl
  | e :: es, acc, hacc => by
    unfold profOK profK
    rw [compA_unpack hacc ht, zcA_unpack (canon_pc hacc ht), profOK_unpack ht es (canon_pc hacc ht),
      CFSG.KC.Fendel.strictB_eq]
    cases h : Nat.beq (zcK P0 P4 EAP (pc acc t)) e
    · have : (zcK P0 P4 EAP (pc acc t) == e) = false := by
        rw [Bool.eq_false_iff]
        intro h'
        rw [beq_iff_eq] at h'
        rw [h', Nat.beq_refl] at h
        exact Bool.noConfusion h
      rw [this]
      rfl
    · have : (zcK P0 P4 EAP (pc acc t) == e) = true := by
        rw [beq_iff_eq]
        exact Nat.eq_of_beq_eq_true h
      rw [this]
      rfl

theorem prodA_unpack {Y : Array (Array Nat)} {Ys : List Nat} {k : Nat}
    (hY : ∀ i < k, Y[i]! = unpack 276 9 (lget Ys i)) (hYc : ∀ i < k, Cn (lget Ys i)) :
    ∀ w : List Nat, (∀ i ∈ w, i < k) → prodA 276 Y w = unpack 276 9 (prodP Ys w) ∧ Cn (prodP Ys w)
  | [], _ => ⟨(idK_sound kId).symm, kCid⟩
  | i :: w, hw => by
    obtain ⟨e, c⟩ := prodA_unpack hY hYc w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hi := hw i (List.mem_cons_self ..)
    refine ⟨?_, canon_pc (hYc i hi) c⟩
    unfold prodA prodP
    rw [e, hY i hi, compA_unpack (hYc i hi) c]

theorem testsOK_unpack {Y : Array (Array Nat)} {Ys : List Nat} {k : Nat}
    (hY : ∀ i < k, Y[i]! = unpack 276 9 (lget Ys i)) (hYc : ∀ i < k, Cn (lget Ys i))
    {ws : List (List Nat × List Nat)} (hw : ∀ p ∈ ws, ∀ i ∈ p.1, i < k) :
    testsOK Y ws = testK P0 P4 EAP Ys ws := by
  unfold testsOK testK
  have key : ∀ p ∈ ws, profOK (prodA 276 Y p.1) (idA 276) p.2 =
      profK P0 P4 EAP (prodP Ys p.1) (pidn 276 9) p.2 := by
    intro p hp
    obtain ⟨e, c⟩ := prodA_unpack hY hYc p.1 (hw p hp)
    rw [e, ← idK_sound kId, profOK_unpack c p.2 kCid]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h p hp => by rw [← key p hp]; exact h p hp,
    fun h p hp => by rw [key p hp]; exact h p hp⟩

theorem profK_spec {t : Nat} : ∀ (es : List Nat) (a : Nat),
    profK P0 P4 EAP t (powR t a) es = true →
      ∀ m < es.length, zcK P0 P4 EAP (powR t (a + m + 1)) = lget es m
  | [], _, _, m, hm => absurd hm (Nat.not_lt_zero m)
  | e :: es, a, h, m, hm => by
    unfold profK at h
    rw [CFSG.KC.Fendel.strictB_eq] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    cases m with
    | zero =>
      exact Nat.eq_of_beq_eq_true h1
    | succ m =>
      have := profK_spec es (a + 1) h2 m (by simpa using hm)
      have e : a + (m + 1) + 1 = a + 1 + m + 1 := by omega
      rw [e]
      exact this

theorem testK_false {Ys : List Nat} {ws : List (List Nat × List Nat)} {u m : Nat}
    (h : failK P0 P4 EAP Ys ws u m = true) : testK P0 P4 EAP Ys ws = false := by
  unfold failK at h
  obtain ⟨hu, h⟩ := (bAnd_iff _ _).1 h
  rw [CFSG.KC.Fendel.strictB_eq] at h
  obtain ⟨hm, h⟩ := (bAnd_iff _ _).1 h
  rw [Bool.eq_false_iff]
  intro ht
  unfold testK at ht
  have hu' : u < ws.length := Nat.le_of_ble_eq_true hu
  have hp := List.all_eq_true.1 ht (ws.getD u ([], [])) (by
    rw [List.getD_eq_getElem _ _ hu']
    exact List.getElem_mem hu')
  have := profK_spec _ 0 hp m (Nat.le_of_ble_eq_true hm)
  rw [Nat.zero_add] at this
  rw [this] at h
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem expProf_unpack {t : Nat} (ht : Cn t) :
    expProf (unpack 276 9 t) = (List.range 24).map fun m => swapZ (zcK P0 P4 EAP (powR t (m + 1))) := by
  unfold expProf
  refine List.map_congr_left fun m _ => ?_
  rw [powA_unpack ht, zcA_unpack (powR_canon ht _)]

end CertificateChecks.KernelLC.Co3Id

end
