
module

public import Certificates.Kernel.LocalComp.Co3IdentElts
public import CFSG.Certificates.Kernel.E3Sound
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigidBase
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.L34KSnd.Tab
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

@[expose] noncomputable def prodP1 (Ys : List Nat) : List Nat → Nat
  | [] => pidn 276 9
  | [i] => lget Ys i
  | i :: j :: w => pc (lget Ys i) (prodP1 Ys (j :: w))

@[expose] noncomputable def powR1 (t : Nat) : Nat → Nat
  | 0 => pidn 276 9
  | 1 => t
  | m + 2 => pc (powR1 t (m + 1)) t

@[expose] noncomputable def failK1 (A Z EA : Nat) (Ys : List Nat) (ws : List (List Nat × List Nat))
    (u m : Nat) : Bool :=
  bAnd(Nat.blt u ws.length, strictB (prodP1 Ys (ws.getD u ([], [])).1) (fun t =>
    bAnd(Nat.blt m (ws.getD u ([], [])).2.length,
      bIf(Nat.beq (zcK A Z EA (powR1 t (Nat.succ m))) (lget (ws.getD u ([], [])).2 m), false, true))))

theorem pc_idR {p : Nat} (hp : Cn p) : pc p (pidn 276 9) = p := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hp
  unfold pc
  exact CFSG.KC.L34KSnd.eq_of_pg (canon_pc hp kCid) hp fun i hi => by
    rw [CFSG.KC.L34KSnd.pg_pcomp' hp hi, CFSG.KC.L34KSnd.pg_pidn' hsz hi]

theorem pc_idL {p : Nat} (hp : Cn p) : pc (pidn 276 9) p = p := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hp
  unfold pc
  exact CFSG.KC.L34KSnd.eq_of_pg (canon_pc kCid hp) hp fun i hi => by
    rw [CFSG.KC.L34KSnd.pg_pcomp' kCid hi, CFSG.KC.L34KSnd.pg_pidn' hsz (CFSG.KC.L34KSnd.canon_lt hp hi)]

theorem prodP1_eq {Ys : List Nat} : ∀ w : List Nat, (∀ i ∈ w, Cn (lget Ys i)) →
    prodP1 Ys w = prodP Ys w ∧ Cn (prodP Ys w)
  | [], _ => ⟨rfl, kCid⟩
  | [i], hw => by
    have hi := hw i (List.mem_singleton_self i)
    exact ⟨(pc_idR hi).symm, canon_pc hi kCid⟩
  | i :: j :: w, hw => by
    have hi := hw i (List.mem_cons_self ..)
    obtain ⟨e, c⟩ := prodP1_eq (j :: w) fun k hk => hw k (List.mem_cons_of_mem _ hk)
    refine ⟨?_, canon_pc hi c⟩
    rw [prodP1, e]
    rfl

theorem powR1_eq {t : Nat} (ht : Cn t) : ∀ m, powR1 t (m + 1) = powR t (m + 1)
  | 0 => (pc_idL ht).symm
  | m + 1 => by
    rw [powR1, powR1_eq ht m]
    rfl

theorem failK1_eq {Ys : List Nat} {ws : List (List Nat × List Nat)} {k u m : Nat}
    (hYc : ∀ i < k, Cn (lget Ys i)) (hw : ∀ p ∈ ws, ∀ i ∈ p.1, i < k) :
    failK1 P0 P4 EAP Ys ws u m = failK P0 P4 EAP Ys ws u m := by
  unfold failK1 failK
  cases hu : Nat.blt u ws.length
  · rfl
  have hu' : u < ws.length := Nat.le_of_ble_eq_true hu
  have hp : ws.getD u ([], []) ∈ ws := by
    rw [List.getD_eq_getElem _ _ hu']
    exact List.getElem_mem hu'
  obtain ⟨e, c⟩ := prodP1_eq (Ys := Ys) _ fun i hi => hYc i (hw _ hp i hi)
  rw [CFSG.KC.Fendel.strictB_eq, CFSG.KC.Fendel.strictB_eq, e, powR1_eq c]

theorem zcK_zero {A Z EA X : Nat} (h : zcK A Z EA X = 0) : X = pidn 276 9 := by
  unfold zcK at h
  cases h0 : Nat.beq X (pidn 276 9)
  · rw [h0] at h
    generalize Nat.beq X Z = b1 at h
    generalize Nat.beq X A = b2 at h
    generalize Nat.beq X EA = b3 at h
    cases b1 <;> cases b2 <;> cases b3 <;> exact absurd h (by decide)
  · exact Nat.eq_of_beq_eq_true h0

theorem profK_app {A Z EA t : Nat} (rest : List Nat) (hr : profK A Z EA t (pidn 276 9) rest = true) :
    ∀ (es : List Nat) (acc : Nat), profK A Z EA t acc es = true → es.getLast? = some 0 →
      profK A Z EA t acc (es ++ rest) = true
  | [], _, _, hl => by simp at hl
  | [e], acc, h, hl => by
    have he : e = 0 := by simpa using hl
    subst he
    unfold profK at h
    rw [CFSG.KC.Fendel.strictB_eq] at h
    obtain ⟨h1, _⟩ := (bAnd_iff _ _).1 h
    rw [List.singleton_append]
    unfold profK
    rw [CFSG.KC.Fendel.strictB_eq, h1, zcK_zero (Nat.eq_of_beq_eq_true h1)]
    exact (bAnd_iff _ _).2 ⟨rfl, hr⟩
  | e :: e' :: es, acc, h, hl => by
    unfold profK at h
    rw [CFSG.KC.Fendel.strictB_eq] at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have ih := profK_app rest hr (e' :: es) _ h2 (by simpa using hl)
    rw [List.cons_append]
    unfold profK
    rw [CFSG.KC.Fendel.strictB_eq]
    exact (bAnd_iff _ _).2 ⟨h1, ih⟩

end CertificateChecks.KernelLC.Co3Id

end
