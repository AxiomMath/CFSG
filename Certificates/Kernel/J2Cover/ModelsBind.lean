
module

public import Certificates.Kernel.J2Cover.ModelsP
public import Certificates.Kernel.J2Cover.Orb
public import Certificates.Kernel.J2Cover.ClassOf
public import Certificates.Kernel.LocalComp.Child3Lemmas
public import Certificates.Kernel.LocalComp.BlockGen
public import CFSG.Certificates.Kernel.DecTextSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.J2Cover.Models

theorem getElem!_ofFn' {α : Type} [Inhabited α] {n : Nat} {f : Fin n → α} {i : Nat} (h : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos _ i (by simp [h]), Array.getElem_ofFn]

theorem getElem!_unpack {n w P i : Nat} (h : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  unfold unpack
  rw [getElem!_ofFn' h]

theorem natsOf_bind {a : Array Nat} {cs : List Char} {n w P : Nat}
    (ha : a = CFSG.Sporadic.Fi23.Native.natsOf (String.ofList cs)) (hd : digitsOK cs = true)
    (hb : arrBind (natsK cs).toArray n w P = true) : a = unpack n w P := by
  rw [ha, natsOf_ofList hd]
  exact arrBind_sound hb

theorem cosetPar_eq : cosetPar = unpack 4725 13 CPP := natsOf_bind NCP.eq (by quickRfl) (by quickRfl)

theorem cosetLab_eq : cosetLab = unpack 4725 1 CLP := natsOf_bind NCL.eq (by quickRfl) (by quickRfl)

@[expose] noncomputable def letP (k : Nat) : Nat := nIf(Nat.beq k 0, PA.S 0, PA.S 1)

theorem cA : CnN 315 9 (PA.S 0) := by quickRfl

theorem cB : CnN 315 9 (PA.S 1) := by quickRfl

theorem cId : CnN 315 9 (pidn 315 9) := by quickRfl

theorem hId : unpack 315 9 (pidn 315 9) = idA 315 := idK_sound (by quickRfl)

theorem letP_canon : ∀ k, CnN 315 9 (letP k)
  | 0 => cA
  | _ + 1 => cB

theorem letter_eq : ∀ k, letterArr k = unpack 315 9 (letP k)
  | 0 => by
    unfold letterArr
    rw [ite_eq_left rfl, alphaArr_eq]
    rfl
  | k + 1 => by
    unfold letterArr
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.succ_ne_zero k)), betaArr_eq]
    rfl

@[expose] noncomputable def wordP (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 315 9) (fun k _ ih => pcomp 315 9 (mask 9) (letP k) ih) w

theorem wordP_canon : ∀ w, CnN 315 9 (wordP w)
  | [] => cId
  | k :: w => canon_pcN (letP_canon k) (wordP_canon w)

theorem wordArr_eq : ∀ w : List Nat, wordArr w = unpack 315 9 (wordP w)
  | [] => hId.symm
  | k :: w => by
    have e : wordArr (k :: w) = compA 315 (letterArr k) (wordArr w) := rfl
    rw [e, wordArr_eq w, letter_eq k, compA_unpackN (letP_canon k) (wordP_canon w)]
    rfl

theorem wordP_append : ∀ (w : List Nat) (l : Nat),
    wordP (w ++ [l]) = pcomp 315 9 (mask 9) (wordP w) (letP l)
  | [], l => (pcomp_id (letP_canon l)).1.trans (pcomp_id (letP_canon l)).2.symm
  | k :: w, l => by
    have e : wordP (k :: w ++ [l]) = pcomp 315 9 (mask 9) (letP k) (wordP (w ++ [l])) := rfl
    rw [e, wordP_append w l]
    exact (pcomp_assoc (letP_canon k) (wordP_canon w) (letP_canon l)).symm

theorem kY : allN 3 (fun k => Nat.beq (wordP (nth [] yWords k)) (YT k)) = true := by quickRfl

theorem kYc : allN 3 (fun k => canonK 315 9 (mask 9) (315 * 9) (YT k)) = true := by quickRfl

theorem yArrs_eq (k : Nat) (hk : k < 3) : yArrs[k]! = unpack 315 9 (YT k) := by
  unfold yArrs
  rw [getElem!_ofFn' hk, wordArr_eq, Nat.eq_of_beq_eq_true (allN_spec kY k hk)]

theorem nth_lt {d b : Nat} (hd : d < b) :
    ∀ (l : List Nat), allL (fun x => Nat.blt x b) l = true → ∀ k, nth d l k < b
  | [], _, _ => hd
  | x :: l, h, k => by
    have h' : bAnd(Nat.blt x b, allL (fun x => Nat.blt x b) l) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    cases k with
    | zero => exact Nat.le_of_ble_eq_true h1
    | succ k => exact nth_lt hd l h2 k

theorem kGen : allL (fun x => Nat.blt x 3) genT = true := by quickRfl

theorem gen_lt (z : Nat) : gen z < 3 := nth_lt (by norm_num) genT kGen z

@[expose] noncomputable def eltPF (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 315 9)
    (fun z _ ih => pcomp 315 9 (mask 9) (YT (gen z)) ih) L

theorem eltPF_eq : ∀ L : List Nat,
    L.foldr (fun z acc => compA 315 yArrs[gen z]! acc) (idA 315) = unpack 315 9 (eltPF L) ∧
      CnN 315 9 (eltPF L)
  | [] => ⟨hId.symm, cId⟩
  | z :: L => by
    obtain ⟨e, c⟩ := eltPF_eq L
    have cy := allN_spec kYc (gen z) (gen_lt z)
    refine ⟨?_, canon_pcN cy c⟩
    rw [List.foldr_cons, e, yArrs_eq (gen z) (gen_lt z), compA_unpackN cy c]
    rfl

theorem kEL : allN 128 (fun x => Nat.beq (eltPF (path x)) (ELT x)) = true := by quickRfl

theorem eltArrs_eq (x : Nat) (hx : x < 128) : eltArrs[x]! = unpack 315 9 (ELT x) := by
  unfold eltArrs
  rw [getElem!_ofFn' hx]
  unfold eltArr
  rw [(eltPF_eq (path x)).1, Nat.eq_of_beq_eq_true (allN_spec kEL x hx)]

theorem eltT_canon (x : Nat) (hx : x < 128) : CnN 315 9 (ELT x) := by
  rw [← Nat.eq_of_beq_eq_true (allN_spec kEL x hx)]
  exact (eltPF_eq (path x)).2

@[expose] noncomputable def cpK (i : Nat) : Nat := pg 13 (mask 13) CPP i

@[expose] noncomputable def clK (i : Nat) : Nat := pg 1 (mask 1) CLP i

@[expose] noncomputable def dpK (i : Nat) : Nat := pg 6 (mask 6) DPP i

@[expose] noncomputable def repTK (i : Nat) : Bool :=
  bAnd(Nat.blt (dpK i) 64, bAnd(canonK 315 9 (mask 9) (315 * 9) (RPT i),
    bIf(Nat.beq i 0, Nat.beq (RPT 0) (pidn 315 9),
      bAnd(Nat.blt (cpK i) 4725, bAnd(Nat.blt (dpK (cpK i)) (dpK i),
        Nat.beq (RPT i) (pcomp 315 9 (mask 9) (RPT (cpK i)) (letP (clK i))))))))

#lc_blocks RPB repTK 4725 64

theorem rep_all (i : Nat) (hi : i < 4725) : repTK i = true :=
  CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RPB.all i hi

theorem rep_facts (i : Nat) (hi : i < 4725) : dpK i < 64 ∧ CnN 315 9 (RPT i) ∧
    (i = 0 → RPT 0 = pidn 315 9) ∧ (i ≠ 0 → cpK i < 4725 ∧ dpK (cpK i) < dpK i ∧
      RPT i = pcomp 315 9 (mask 9) (RPT (cpK i)) (letP (clK i))) := by
  have h := rep_all i hi
  unfold repTK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.le_of_ble_eq_true h1, h2, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    exact Nat.eq_of_beq_eq_true h
  · have hb : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
    rw [hb] at h
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
    exact ⟨Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem cosetWordAux_eq : ∀ (n i : Nat), i < 4725 → dpK i < n → wordP (cosetWordAux n i) = RPT i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hi, hd => by
    obtain ⟨-, -, h0, h1⟩ := rep_facts i hi
    unfold cosetWordAux
    by_cases hz : i = 0
    · subst hz
      rw [ite_eq_left rfl, h0 rfl]
      rfl
    · obtain ⟨hp, hdp, he⟩ := h1 hz
      rw [ite_eq_right_of_eq_false _ _ (eq_false hz), cosetPar_eq, cosetLab_eq,
        getElem!_unpack hi, getElem!_unpack hi, wordP_append]
      change pcomp 315 9 (mask 9) (wordP (cosetWordAux n (cpK i))) (letP (clK i)) = RPT i
      rw [cosetWordAux_eq n (cpK i) hp (by omega), he]

theorem repArrs_eq (i : Nat) (hi : i < 4725) : repArrs[i]! = unpack 315 9 (RPT i) := by
  unfold repArrs
  rw [getElem!_ofFn' hi, wordArr_eq]
  unfold cosetWord
  rw [cosetWordAux_eq 64 i hi (rep_facts i hi).1]

theorem repT_canon (i : Nat) (hi : i < 4725) : CnN 315 9 (RPT i) := (rep_facts i hi).2.1

end CertificateChecks.KernelJ2Cover

end
