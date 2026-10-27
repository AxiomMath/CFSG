module

public import Certificates.Kernel.LocalQT.M23D.Gens
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.KD.LQT.M23D

open Equiv CFSG.QuasithinUnique.Vol2Native.L239.Covers CFSG.Sporadic.Schreier CFSG.Blueprint
open scoped Pointwise

@[expose] def keyE (e : Finset (Fin 23) × Fin 2) : ℕ := 2 * enc e.1 + e.2.val

theorem keyE_injective : Function.Injective keyE := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  have h' : 2 * enc s + i.val = 2 * enc t + j.val := h
  have h1 : (i : ℕ) = j := by omega
  have h2 : enc s = enc t := by omega
  rw [enc_injective h2, Fin.ext h1]

@[expose] noncomputable def keyStep (l : Letter) (p : ℕ × List ℕ) : ℕ × List ℕ :=
  Prod.rec (motive := fun _ => ℕ × List ℕ) (fun e ks =>
    Prod.rec (motive := fun _ => ℕ × List ℕ) (fun i b =>
      letN (pm (codeL i b) e) fun e' =>
        letN (Nat.add (Nat.mul (nat_lit 2) (Bool.rec (motive := fun _ => ℕ) e' e b)) i.val)
          fun k => (e', k :: ks)) l) p

@[expose] noncomputable def keysW (w : List Letter) (m : ℕ) : ℕ × List ℕ :=
  List.rec (motive := fun _ => ℕ × List ℕ) (m, []) (fun l _ ih => keyStep l ih) w

theorem keyStep_eq (i : Fin 2) (b : Bool) (e : ℕ) (ks : List ℕ) :
    keyStep (i, b) (e, ks) =
      (pm (codeL i b) e, (2 * (if b then e else pm (codeL i b) e) + i.val) :: ks) := by
  change letN (pm (codeL i b) e) (fun e' =>
    letN (Nat.add (Nat.mul 2 (Bool.rec (motive := fun _ => ℕ) e' e b)) i.val)
      fun k => (e', k :: ks)) = _
  rw [letN_eq, letN_eq]
  cases b <;> rfl

theorem keysW_enc (w : List Letter) (s : Finset (Fin 23)) :
    keysW w (enc s) = (enc (pathEnd gM w s), (wordKeys gM w s).map keyE) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    change keyStep (i, b) (keysW w (enc s)) = _
    rw [ih, keyStep_eq, pm_letter]
    simp only [pathEnd, wordKeys, List.map_cons]
    cases b
    · simp [letterKey, letterVal, keyE]
    · simp [letterKey, keyE]

@[expose] noncomputable def cellKeysK (C : List (Finset (Fin 23) × Fin 9)) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun p _ ih => appK (keysW (m23Rw p.2) (enc p.1)).2 ih) C

theorem cellKeysK_eq (C : List (Finset (Fin 23) × Fin 9)) :
    cellKeysK C =
      ((C.map fun p => (p.1, m23Rw p.2)).flatMap fun c => wordKeys gM c.2 c.1).map keyE := by
  induction C with
  | nil => rfl
  | cons p C ih =>
    change appK (keysW (m23Rw p.2) (enc p.1)).2 (cellKeysK C) = _
    rw [appK_eq, ih, keysW_enc]
    simp [List.flatMap_cons, List.map_append]

theorem cellKeysK_cyc (k : Fin 7) : cellKeysK (cycCells k) = (cycKeys k).map keyE :=
  cellKeysK_eq _

@[expose] noncomputable def tog1 (x : ℕ) (acc : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [x]
    (fun y ys ih => Bool.rec (motive := fun _ => List ℕ) (y :: ih) ys (Nat.beq x y)) acc

@[expose] noncomputable def togAll (L : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun x _ ih acc => ih (tog1 x acc)) L

@[expose] noncomputable def evenK (L : List ℕ) : Bool := isNilK (togAll L [])

theorem tog1_count (x z : ℕ) (acc : List ℕ) :
    (tog1 x acc).count z % 2 = (acc.count z + if x = z then 1 else 0) % 2 := by
  induction acc with
  | nil =>
    change [x].count z % 2 = _
    simp only [List.count_singleton, beq_iff_eq, List.count_nil]
    split_ifs <;> omega
  | cons y ys ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (y :: tog1 x ys) ys (Nat.beq x y)).count z % 2 = _
    cases h : Nat.beq x y
    · change (y :: tog1 x ys).count z % 2 = _
      simp only [List.count_cons, beq_iff_eq] at ih ⊢
      split_ifs at ih ⊢ <;> omega
    · have hxy : x = y := Nat.eq_of_beq_eq_true h
      subst hxy
      change ys.count z % 2 = _
      simp only [List.count_cons, beq_iff_eq]
      split_ifs <;> omega

theorem togAll_count (L : List ℕ) (z : ℕ) :
    ∀ acc : List ℕ, (togAll L acc).count z % 2 = (acc.count z + L.count z) % 2 := by
  induction L with
  | nil => intro acc; simp [togAll]
  | cons x L ih =>
    intro acc
    change (togAll L (tog1 x acc)).count z % 2 = _
    have h1 := ih (tog1 x acc)
    have h2 := tog1_count x z acc
    simp only [List.count_cons, beq_iff_eq] at h2 ⊢
    split_ifs at h2 ⊢ <;> omega

theorem evenK_true {L : List ℕ} (h : evenK L = true) (z : ℕ) : Even (L.count z) := by
  have h0 := togAll_count L z []
  rw [isNilK_true h] at h0
  simp only [List.count_nil, zero_add] at h0
  exact Nat.even_iff.2 h0.symm

theorem cycOK : allK (fun k => evenK (cellKeysK (cycCells k))) (List.finRange 7) = true := by
  quickRfl

theorem cycKeys_even : (List.finRange 7).all (fun k => allEven (cycKeys k)) = true := by
  rw [List.all_eq_true]
  intro k hk
  have hk' := allK_true _ _ cycOK k hk
  rw [cellKeysK_cyc] at hk'
  unfold allEven
  rw [List.all_eq_true]
  intro e _
  apply decide_eq_true
  rw [← List.count_map_of_injective _ keyE keyE_injective]
  exact evenK_true hk' _

end CFSG.KD.LQT.M23D
