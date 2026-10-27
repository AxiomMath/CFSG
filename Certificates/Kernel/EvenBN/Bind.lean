
module

public import Certificates.Kernel.SporSch.Tits.Central2263
public import Certificates.Kernel.SporSch.Tits.GenList
public import Certificates.Data.TitsAschbacherParrott
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinUnpack
meta import Certificates.Data.TitsAschbacherParrott
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN

meta def vList : List (Array Nat) := Certificates.TitsAschbacherParrott.vArrs.toList

end CertificateChecks.KernelEvenBN

#kst_plist CertificateChecks.KernelEvenBN.VL 11 CertificateChecks.KernelEvenBN.vList
#ks_perm CertificateChecks.KernelEvenBN.Pi 11 CFSG.Quasithin.titsPiArr
#ks_perm CertificateChecks.KernelEvenBN.PiI 11 CFSG.Quasithin.piInv
#ks_perm CertificateChecks.KernelEvenBN.W1 11 Certificates.TitsAschbacherParrott.w1Arr
#ks_perm CertificateChecks.KernelEvenBN.W2 11 Certificates.TitsAschbacherParrott.w2Arr

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Quasithin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelSporSch.TitsCentral
open Certificates.TitsAschbacherParrott

@[expose] noncomputable def wP (G : Nat → Nat) (w : List Nat) : Nat :=
  wordTabK 1755 11 (mask 11) (pidn 1755 11) G w

@[expose] noncomputable def V (i : Nat) : Nat := CFSG.KS.Mathieu.nget VL i

@[expose] noncomputable def ppw (p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 1755 11) (fun _ acc => pcomp 1755 11 (mask 11) p acc) k

@[expose] noncomputable def listK (n P : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i n)
    (fun x _ ih i => bAnd(Nat.beq x (pg 11 (mask 11) P i), ih (Nat.succ i)))

theorem listK_spec {n P : Nat} : ∀ (l : List Nat) (k : Nat), listK n P l k = true →
    k + l.length = n ∧ ∀ i (h : i < l.length), l[i] = pg 11 (mask 11) P (k + i)
  | [], k, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun i h => absurd h (by simp)⟩
  | x :: l, k, h => by
    have h' : bAnd(Nat.beq x (pg 11 (mask 11) P k), listK n P l (Nat.succ k)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨e1, e2⟩ := listK_spec l (k + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ i =>
      rw [List.getElem_cons_succ, e2 i (by simpa using hi)]
      congr 1
      omega

theorem arr_of_listK {a : Array Nat} {P : Nat} (h : listK 1755 P a.toList 0 = true) :
    a = unpack 1755 11 P := by
  obtain ⟨e1, e2⟩ := listK_spec a.toList 0 h
  simp only [Nat.zero_add, Array.length_toList] at e1 e2
  apply Array.ext
  · simp [unpack, e1]
  · intro i h1 h2
    have := e2 i h1
    rw [Array.getElem_toList] at this
    rw [this]
    simp [unpack]

theorem prod_eq {A : Array (Array Nat)} {G : Nat → Nat} {w : List Nat}
    (h : ∀ j ∈ w, A[j]! = unpack 1755 11 (G j) ∧ C (G j)) :
    prodArr A w = unpack 1755 11 (wP G w) ∧ C (wP G w) :=
  wordTabK_eq TitsCentral.id_eq canId w h

theorem chain_gen {A : Array (Array Nat)} {PS : Nat → Nat} {kS nb BP : Nat} {base : Array Nat}
    (hb : Binds 1755 11 PS kS nb BP A base)
    (hc : allN kS (fun j => canonK 1755 11 (mask 11) (1755 * 11) (PS j)) = true) {w : List Nat}
    (hw : ∀ j ∈ w, j < kS) : prodArr A w = unpack 1755 11 (wP PS w) ∧ C (wP PS w) :=
  prod_eq fun j hj => ⟨hb.2.2.2.2.1 j (hw j hj), allN_spec hc j (hw j hj)⟩

theorem cmpU {p q : Nat} (hp : canonK 1755 11 (mask 11) (1755 * 11) p = true)
    (hq : canonK 1755 11 (mask 11) (1755 * 11) q = true) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pcomp 1755 11 (mask 11) p q) :=
  compA_unpack hp hq

theorem cmpC {p q : Nat} (hp : canonK 1755 11 (mask 11) (1755 * 11) p = true)
    (hq : canonK 1755 11 (mask 11) (1755 * 11) q = true) :
    canonK 1755 11 (mask 11) (1755 * 11) (pcomp 1755 11 (mask 11) p q) = true :=
  canonK_pcomp hp hq

theorem eqU {p q : Nat} (hp : canonK 1755 11 (mask 11) (1755 * 11) p = true)
    (hq : canonK 1755 11 (mask 11) (1755 * 11) q = true) :
    eqA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = Nat.beq p q :=
  eqA_unpack hp hq

theorem powUC {p : Nat} (hp : C p) :
    ∀ k, powA (unpack 1755 11 p) k = unpack 1755 11 (ppw p k) ∧ C (ppw p k)
  | 0 => ⟨TitsCentral.id_eq, canId⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := powUC hp k
    refine ⟨?_, canonK_pcomp hp h2⟩
    unfold powA at h1 ⊢
    rw [List.replicate_succ, List.foldr_cons, h1]
    exact compA_unpack hp h2

theorem powU {p k : Nat} (hp : canonK 1755 11 (mask 11) (1755 * 11) p = true) :
    powA (unpack 1755 11 p) k = unpack 1755 11 (ppw p k) := (powUC hp k).1

theorem powC {p k : Nat} (hp : canonK 1755 11 (mask 11) (1755 * 11) p = true) :
    canonK 1755 11 (mask 11) (1755 * 11) (ppw p k) = true := (powUC hp k).2

theorem piL : listK 1755 Pi titsPiArr.toList 0 = true := by quickRfl
theorem cPi : C Pi := by quickRfl
theorem cPiI : C PiI := by quickRfl
theorem piP : permOK 1755 11 (mask 11) (1755 * 11) Pi PiI = true := by quickRfl

theorem pi_eq : titsPiArr = unpack 1755 11 Pi := arr_of_listK piL

theorem piInv_eq : piInv = unpack 1755 11 PiI := by
  unfold piInv
  rw [pi_eq]
  exact (invEqK_sound piP).1

theorem opt_eq (o : Bool) : (if o = true then titsPiArr else idA 1755) =
    unpack 1755 11 (Bool.rec (motive := fun _ => Nat) (pidn 1755 11) Pi o) ∧
    C (Bool.rec (motive := fun _ => Nat) (pidn 1755 11) Pi o) := by
  cases o
  · exact ⟨TitsCentral.id_eq, canId⟩
  · exact ⟨pi_eq, cPi⟩

theorem vOK : allN 13 (fun i => Nat.beq (pcomp 1755 11 (mask 11)
    (wP TitsS.S (parrottWords.getD i ([], false)).1)
    (Bool.rec (motive := fun _ => Nat) (pidn 1755 11) Pi (parrottWords.getD i ([], false)).2))
    (V i)) = true := by quickRfl

theorem vLet : ∀ i < 13, ∀ j ∈ (parrottWords.getD i ([], false)).1, j < 9 := by decide

theorem v_eq {i : Nat} (hi : i < 13) : vArrs[i]! = unpack 1755 11 (V i) ∧ C (V i) := by
  have e := Nat.eq_of_beq_eq_true (allN_spec vOK i hi)
  obtain ⟨h1, c1⟩ := chain_gen bindsS canS (vLet i hi)
  obtain ⟨h2, c2⟩ := opt_eq (parrottWords.getD i ([], false)).2
  rw [← e]
  refine ⟨?_, canonK_pcomp c1 c2⟩
  unfold vArrs
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  change compA 1755 (prodArr titsSArrs (parrottWords.getD i ([], false)).1)
    (if (parrottWords.getD i ([], false)).2 = true then titsPiArr else idA 1755) = _
  rw [h1, h2]
  exact compA_unpack c1 c2

theorem vA_eq {i : Nat} (hi : i < 13) : vA i = unpack 1755 11 (V i) := (v_eq hi).1

theorem cV {i : Nat} (hi : i < 13) : canonK 1755 11 (mask 11) (1755 * 11) (V i) = true :=
  (v_eq hi).2

theorem vTab : ∀ j ∈ (List.range 13), vArrs[j]! = unpack 1755 11 (V j) ∧ C (V j) :=
  fun _ hj => v_eq (List.mem_range.1 hj)

theorem vProd_eq {l : List Nat} (hl : ∀ j ∈ l, j < 13) :
    vProd l = unpack 1755 11 (wP V l) ∧ C (wP V l) :=
  prod_eq fun j hj => v_eq (hl j hj)

theorem canN : allN 10 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (TitsN.S j)) = true := by
  quickRfl

theorem w1B : Nat.beq (wP TitsH.S reeWord₁) W1 = true := by quickRfl
theorem w2B : Nat.beq (wP TitsN.S reeWord₂) W2 = true := by quickRfl

theorem w1_eq : w1Arr = unpack 1755 11 W1 ∧ C W1 := by
  obtain ⟨h1, h2⟩ := chain_gen bindsH canH (w := reeWord₁) (by decide)
  rw [Nat.eq_of_beq_eq_true w1B] at h1 h2
  exact ⟨h1, h2⟩

theorem w2_eq : w2Arr = unpack 1755 11 W2 ∧ C W2 := by
  obtain ⟨h1, h2⟩ := chain_gen bindsN canN (w := reeWord₂) (by decide)
  rw [Nat.eq_of_beq_eq_true w2B] at h1 h2
  exact ⟨h1, h2⟩

theorem negPi : (listK 1755 W1 titsPiArr.toList 0).not = true := by quickRfl
theorem negV : (Nat.beq (pcomp 1755 11 (mask 11) (wP TitsS.S [1, 2, 0, 2, 0, 0]) (pidn 1755 11))
    (V 1)).not = true := by quickRfl
theorem negW : (Nat.beq (wP TitsN.S [3, 2, 2, 1]) W2).not = true := by quickRfl

end CertificateChecks.KernelEvenBN

end
