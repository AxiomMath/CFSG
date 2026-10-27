module

public import Certificates.Kernel.Om2K.ChecksL
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.HexaStabKGlue

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA)
open CertificateChecks.KernelLC.E8 (RT)

theorem band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

abbrev Cn (p : Nat) : Prop := canonK 480 9 (mask 9) (480 * 9) p = true

abbrev Cn2 (p : Nat) : Prop := canonK 240 8 (mask 8) (240 * 8) p = true

theorem okK_iff {p : Nat} (h : okK p = true) :
    Cn p ∧ permOK 480 9 (mask 9) (480 * 9) p (pinv p) = true ∧ Cn (pinv p) := by
  unfold okK at h
  obtain ⟨h1, h2⟩ := band h
  exact ⟨h1, band h2⟩

theorem compA_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 480 (unpack 480 9 p) (unpack 480 9 q) = unpack 480 9 (pc p q) := compA_unpack hp hq

theorem cn_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := canonK_pcomp hp hq

theorem invCand_pinv {p : Nat} (h : okK p = true) :
    invCand 480 (unpack 480 9 p) = unpack 480 9 (pinv p) :=
  invCand_unpack (okK_iff h).2.1

theorem eqA_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    eqA 480 (unpack 480 9 p) (unpack 480 9 q) = Nat.beq p q := eqA_unpack hp hq

theorem idA_eq : idA 480 = unpack 480 9 pid := (idK_sound kId).symm

theorem validA_ok {p : Nat} (h : okK p = true) : validA 480 (unpack 480 9 p) = true :=
  validA_unpack (okK_iff h).2.1

theorem conjA_pc {g y : Nat} (hg : okK g = true) (hy : Cn y) :
    conjA 480 (unpack 480 9 g) (unpack 480 9 y) = unpack 480 9 (pc g (pc y (pinv g))) := by
  obtain ⟨c1, -, c3⟩ := okK_iff hg
  unfold conjA
  rw [invCand_pinv hg, compA_pc hy c3, compA_pc c1 (cn_pc hy c3)]

theorem refl_get {r : Nat} (hr : r < 240) : (reflTab ())[r]! = unpack 240 8 (RT r) := by
  rw [← CertificateChecks.KernelLC.E8.refl_eq r hr]
  unfold reflTab
  rw [getElem!_pos _ r (by simp [hr])]
  simp

theorem cn_RT {r : Nat} (hr : r < 240) : Cn2 (RT r) := allN_spec kRT r hr

theorem idA2_eq : idA 240 = unpack 240 8 (pidn 240 8) := (idK_sound kId2).symm

theorem cn_pid2 : Cn2 (pidn 240 8) := kPid2

theorem get_append_right {a b : Array (Array Nat)} {i : Nat} (h1 : a.size ≤ i)
    (h2 : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  rw [getElem!_pos (a ++ b) i (by simp; omega), getElem!_pos b (i - a.size) (by omega),
    Array.getElem_append_right h1]

theorem get_append_left {a b : Array (Array Nat)} {i : Nat} (h1 : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by simp; omega), getElem!_pos a i h1, Array.getElem_append_left h1]

theorem get_map {a : Array (Array Nat)} {f : Array Nat → Array Nat} {i : Nat} (h : i < a.size) :
    (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using h), getElem!_pos a i h, Array.getElem_map]

theorem wA_eq : ∀ w : List Nat, (∀ r ∈ w, r < 240) →
    wA (reflTab ()) w = unpack 240 8 (wAK w) ∧ Cn2 (wAK w)
  | [], _ => ⟨idA2_eq, cn_pid2⟩
  | r :: w, h => by
    have hr := h r (List.mem_cons_self ..)
    obtain ⟨e, c⟩ := wA_eq w fun s hs => h s (List.mem_cons_of_mem _ hs)
    have hw : wAK (r :: w) = pc2 (RT r) (wAK w) := rfl
    rw [hw]
    refine ⟨?_, canonK_pcomp (cn_RT hr) c⟩
    change compA 240 (reflTab ())[r]! (wA (reflTab ()) w) = _
    rw [refl_get hr, e, compA_unpack (cn_RT hr) c]
    rfl

theorem pg_lt2 {A : Nat} (hA : Cn2 A) {i : Nat} (hi : i < 240) : pg 8 (mask 8) A i < 240 :=
  Nat.blt_eq.mp (allN_spec (range_of_canonK hA) i hi)

theorem pairA_eq {A B : Nat} (hA : Cn2 A) (hB : Cn2 B) :
    pairA (unpack 240 8 A) (unpack 240 8 B) = unpack 480 9 (pairK A B) := by
  have hf : ∀ x < 480, (Bool.rec (motive := fun _ => Nat) (Nat.add (pg 8 255 B (Nat.sub x 240)) 240)
      (pg 8 255 A x) (Nat.blt x 240) : Nat) < 2 ^ 9 := by
    intro x hx
    by_cases h : x < 240
    · have e : Nat.blt x 240 = true := Nat.blt_eq.mpr h
      rw [e]
      have := pg_lt2 hA h
      change pg 8 (mask 8) A x < 2 ^ 9
      omega
    · have e : Nat.blt x 240 = false := by
        cases e' : Nat.blt x 240
        · rfl
        · exact absurd (Nat.blt_eq.mp e') h
      rw [e]
      have := pg_lt2 hB (i := x - 240) (by omega)
      change pg 8 (mask 8) B (x - 240) + 240 < 2 ^ 9
      omega
  unfold pairK
  rw [CFSG.KC.HexaStabK.unpack_pmk (by norm_num) hf]
  apply Array.ext
  · simp [pairA, unpack]
  · intro i h1 h2
    have hs : (unpack 240 8 A).size = 240 := by simp [unpack]
    rw [Array.getElem_ofFn]
    simp only [pairA, Array.getElem_append, hs]
    by_cases h : i < 240
    · have e : Nat.blt i 240 = true := Nat.blt_eq.mpr h
      rw [dif_pos h, e]
      simp [unpack]
      rfl
    · have e : Nat.blt i 240 = false := by
        cases e' : Nat.blt i 240
        · rfl
        · exact absurd (Nat.blt_eq.mp e') h
      rw [dif_neg h, e]
      simp [unpack]
      rfl

theorem omWords_lt : ∀ i < 8, ∀ r ∈ CFSG.EvenSmallLie.OmegaEight.Weyl.omWords.getD i [], r < 240 := by
  decide

theorem yW_lt : ∀ i < 8, ∀ r ∈ yW.getD i [], r < 240 := by decide

theorem genY_get {i : Nat} (hi : i < 8) : (genY (reflTab ()))[i]! = unpack 480 9 (gYK i) := by
  obtain ⟨e1, c1⟩ := wA_eq _ (omWords_lt i hi)
  obtain ⟨e2, c2⟩ := wA_eq _ (yW_lt i hi)
  unfold genY
  rw [getElem!_pos _ i (by simp [hi])]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  rw [e1, e2, pairA_eq c1 c2]
  rfl

theorem L_ok {l : Nat} (hl : l < 16) : okK (L.G l) = true := allN_spec kOkL l hl

theorem letters_get {l : Nat} (hl : l < 16) : (lettersY (reflTab ()))[l]! = unpack 480 9 (L.G l) := by
  have hs : (genY (reflTab ())).size = 8 := by simp [genY]
  unfold lettersY
  by_cases h : l < 8
  · rw [get_append_left (by omega), genY_get h, Nat.eq_of_beq_eq_true (allN_spec kGY l h)]
  · have hj : l - 8 < 8 := by omega
    rw [get_append_right (by omega) (by simp [hs]; omega), hs, get_map (by omega), genY_get hj,
      ← Nat.eq_of_beq_eq_true (allN_spec kGY (l - 8) hj), invCand_pinv (L_ok (by omega))]
    have e := Nat.eq_of_beq_eq_true (allN_spec kInv (l - 8) hj)
    have e2 : Nat.add (l - 8) 8 = l := by
      change l - 8 + 8 = l
      omega
    rw [e2] at e
    rw [e]

theorem wY_eq : ∀ w : List Nat, (∀ l ∈ w, l < 16) →
    wY (lettersY (reflTab ())) w = unpack 480 9 (wYK w) ∧ Cn (wYK w)
  | [], _ => ⟨idA_eq, kPid⟩
  | l :: w, h => by
    have hl := h l (List.mem_cons_self ..)
    obtain ⟨e, c⟩ := wY_eq w fun s hs => h s (List.mem_cons_of_mem _ hs)
    have hw : wYK (l :: w) = pc (L.G l) (wYK w) := rfl
    rw [hw]
    have cl := (okK_iff (L_ok hl)).1
    refine ⟨?_, cn_pc cl c⟩
    change compA 480 (lettersY (reflTab ()))[l]! (wY (lettersY (reflTab ())) w) = _
    rw [letters_get hl, e, compA_pc cl c]

end CertificateChecks.KernelOm2

end
