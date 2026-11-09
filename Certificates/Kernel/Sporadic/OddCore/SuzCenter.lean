module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Spor.HexAtSound
import all CFSG.Certificates.Kernel.Spor.HexAtSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Sporadic.SuzOddCore.GraphArrays
meta import CFSG.Sporadic.SuzOddCore.GraphArrays
import all CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.SuzOddCore.Arrays
meta import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

def suzCen0a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-0a.txt"
def suzCen0b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-0b.txt"
def suzCen1a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-1a.txt"
def suzCen1b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-1b.txt"
def suzCen2a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-2a.txt"
def suzCen2b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-2b.txt"
def suzCen3a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-3a.txt"
def suzCen3b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-3b.txt"
def suzCen4a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-4a.txt"
def suzCen4b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-4b.txt"
def suzCen5a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-5a.txt"
def suzCen5b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-5b.txt"
def suzCen6a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-6a.txt"
def suzCen6b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-6b.txt"
def suzCen7a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-7a.txt"
def suzCen7b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-7b.txt"
def suzCen8a : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-8a.txt"
def suzCen8b : String := include_str "../../../Data/CFSGNative/SuzOddCore/suz-graph-center-8b.txt"

end CertificateChecks.KernelSpor.OddCore

#ks_chars CertificateChecks.KernelSpor.SuzCenT CFSG.Sporadic.SuzOddCore.graphCenterText
#ks_chars CertificateChecks.KernelSpor.SuzCenTA0 CertificateChecks.KernelSpor.OddCore.suzCen0a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB0 CertificateChecks.KernelSpor.OddCore.suzCen0b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA1 CertificateChecks.KernelSpor.OddCore.suzCen1a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB1 CertificateChecks.KernelSpor.OddCore.suzCen1b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA2 CertificateChecks.KernelSpor.OddCore.suzCen2a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB2 CertificateChecks.KernelSpor.OddCore.suzCen2b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA3 CertificateChecks.KernelSpor.OddCore.suzCen3a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB3 CertificateChecks.KernelSpor.OddCore.suzCen3b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA4 CertificateChecks.KernelSpor.OddCore.suzCen4a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB4 CertificateChecks.KernelSpor.OddCore.suzCen4b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA5 CertificateChecks.KernelSpor.OddCore.suzCen5a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB5 CertificateChecks.KernelSpor.OddCore.suzCen5b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA6 CertificateChecks.KernelSpor.OddCore.suzCen6a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB6 CertificateChecks.KernelSpor.OddCore.suzCen6b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA7 CertificateChecks.KernelSpor.OddCore.suzCen7a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB7 CertificateChecks.KernelSpor.OddCore.suzCen7b
#ks_chars CertificateChecks.KernelSpor.SuzCenTA8 CertificateChecks.KernelSpor.OddCore.suzCen8a
#ks_chars CertificateChecks.KernelSpor.SuzCenTB8 CertificateChecks.KernelSpor.OddCore.suzCen8b

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore

meta def rowsOfC (r : Nat) (t : Array Nat) : Array (Array Nat) :=
  (List.range r).toArray.map fun j => t.extract (32 * j) (32 * j + 32)

meta def cenRowsM : Array (Array Nat) :=
  ((List.range 9).toArray.map fun r => rowsOfC 715 (centerFull r)).flatten

meta def cenInvRowsM : Array (Array Nat) :=
  ((List.range 9).toArray.map fun r =>
    rowsOfC 715 (CFSG.Monster.B.Co2.Native.invCand 22880 (centerFull r))).flatten

meta def cenCompM : Array (Array Nat) := (List.range 9).toArray.map centerCompact

meta def cenCompInvM : Array (Array Nat) :=
  cenCompM.map (CFSG.Monster.B.Co2.Native.invCand 280)

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenR CertificateChecks.KernelSpor.OddCore.cenRowsM 15

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenRI CertificateChecks.KernelSpor.OddCore.cenInvRowsM 15

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenC CertificateChecks.KernelSpor.OddCore.cenCompM 9

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCenCI CertificateChecks.KernelSpor.OddCore.cenCompInvM 9

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Row CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Misc.HexAt

@[expose] noncomputable def fullB (r : Nat) : Bool :=
  hexAtK SuzCenT.chars (Nat.mul 4 (Nat.mul 23090 r)) 4 32 15 715 (offF SuzCenR (Nat.mul 715 r))

@[expose] noncomputable def compB (r : Nat) : Bool :=
  hexAtK SuzCenT.chars (Nat.add (Nat.mul 92360 r) 91520) 3 280 9 1 (offF SuzCenC r)

@[expose] noncomputable def cenPieces : List (List Char) :=
  [SuzCenTA0.chars, SuzCenTB0.chars, SuzCenTA1.chars, SuzCenTB1.chars, SuzCenTA2.chars,
    SuzCenTB2.chars, SuzCenTA3.chars, SuzCenTB3.chars, SuzCenTA4.chars, SuzCenTB4.chars,
    SuzCenTA5.chars, SuzCenTB5.chars, SuzCenTA6.chars, SuzCenTB6.chars, SuzCenTA7.chars,
    SuzCenTB7.chars, SuzCenTA8.chars, SuzCenTB8.chars]

@[expose] def cenPL (k : Nat) : Nat := 91520 - 90680 * (k % 2)

@[expose] noncomputable def cenPreK (n : Nat) (p : List Char) :
    List Char → Nat → (List Char → Bool) → Bool :=
  List.rec (motive := fun _ => List Char → Nat → (List Char → Bool) → Bool)
    (fun cs a k => bAnd(Nat.beq a n, k cs))
    (fun ch _ ih cs a k => List.casesOn (motive := fun _ => Bool) cs false
      (fun c t => bAnd(Nat.beq (Char.toNat ch) (Char.toNat c),
        strictB (Nat.succ a) (fun a' => ih t a' k))))
    p

theorem cenPreK_sound {n a : Nat} {p cs : List Char} {k : List Char → Bool}
    (h : cenPreK n p cs a k = true) : p.length + a = n ∧ ∃ s, cs = p ++ s ∧ k s = true := by
  induction p generalizing cs a with
  | nil =>
    have h' : Bool.rec (motive := fun _ => Bool) false (k cs) (Nat.beq a n) = true := h
    rw [bAnd_iff] at h'
    exact ⟨by simpa using Nat.beq_eq.mp h'.1, cs, rfl, h'.2⟩
  | cons ch p ih =>
    cases cs with
    | nil => exact absurd h Bool.false_ne_true
    | cons c t =>
      have h' : Bool.rec (motive := fun _ => Bool) false
          (strictB (Nat.succ a) (fun a' => cenPreK n p t a' k))
          (Nat.beq (Char.toNat ch) (Char.toNat c)) = true := h
      simp only [bAnd_iff, CFSG.KS.PackFld.strictB_eqP] at h'
      obtain ⟨hc, ht⟩ := h'
      obtain ⟨hl, s, rfl, hs⟩ := ih ht
      refine ⟨?_, s, ?_, hs⟩
      · simp only [List.length_cons]
        omega
      · rw [Char.toNat_inj.mp (Nat.beq_eq.mp hc).symm]
        rfl

theorem hexAtK_skipAscii {A B : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (hA : ∀ c ∈ A, c.toNat < 128) (h : hexAtK B off d n w N F = true) :
    hexAtK (A ++ B) (A.length + off) d n w N F = true := by
  induction A with
  | nil => simpa using h
  | cons c A ih =>
    rw [List.cons_append, List.length_cons, Nat.add_right_comm,
      hexAtK_succ_cons c (A ++ B) rfl, bAnd_iff]
    exact ⟨Nat.blt_eq.mpr (hA c List.mem_cons_self),
      ih fun x hx => hA x (List.mem_cons_of_mem c hx)⟩

theorem cenBRec_mono {x y x' y' : Bool} (c : Bool) (hx : x = true → x' = true)
    (hy : y = true → y' = true) :
    Bool.rec (motive := fun _ => Bool) x y c = true →
      Bool.rec (motive := fun _ => Bool) x' y' c = true := by
  cases c
  exacts [hx, hy]

@[expose] noncomputable def cenStep (d n w N : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v acc : Nat) : Bool :=
  bIf(Nat.beq j N, true,
    strictB (CFSG.KS.Text.hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
      bIf(Nat.beq (Nat.succ t) d,
        bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
          strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
            bIf(Nat.beq (Nat.succ e) n,
              bAnd(Nat.beq acc' (F j),
                ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
              ih j (Nat.succ e) (nat_lit 0) (nat_lit 0) acc')),
          false),
        ih j e (Nat.succ t) v' acc)),
      false)))

theorem cenRun_append {d n w N : Nat} {F : Nat → Nat} (C : List Char) (B : List Char) :
    ∀ {j e t v acc : Nat}, CFSG.KC.Misc.HexFlat.run d n w N F B j e t v acc = true →
      CFSG.KC.Misc.HexFlat.run d n w N F (B ++ C) j e t v acc = true := by
  induction B with
  | nil =>
    intro j e t v acc h
    have hj : Nat.beq j N = true := h
    cases C with
    | nil => exact hj
    | cons c C =>
      change cenStep d n w N F c (CFSG.KC.Misc.HexFlat.run d n w N F C) j e t v acc = true
      unfold cenStep
      rw [hj]
  | cons c B ih =>
    intro j e t v acc h
    change cenStep d n w N F c (CFSG.KC.Misc.HexFlat.run d n w N F B) j e t v acc = true at h
    change cenStep d n w N F c (CFSG.KC.Misc.HexFlat.run d n w N F (B ++ C)) j e t v acc = true
    unfold cenStep at h ⊢
    simp only [CFSG.KS.PackFld.strictB_eqP] at h ⊢
    refine cenBRec_mono _ ?_ id h
    refine cenBRec_mono _ id ?_
    refine cenBRec_mono _ ih ?_
    refine cenBRec_mono _ id ?_
    exact cenBRec_mono _ ih (cenBRec_mono _ id ih)

theorem hexAtK_append {B C : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (h : hexAtK B off d n w N F = true) : hexAtK (B ++ C) off d n w N F = true := by
  induction off generalizing B with
  | zero =>
    rw [hexAtK_zero] at h ⊢
    unfold CFSG.KC.Misc.HexFlat.hexFlat at h ⊢
    exact cenBRec_mono _ id (cenBRec_mono _ id (cenRun_append C B)) h
  | succ off ih =>
    cases B with
    | nil =>
      rw [hexAtK_succ_nil] at h
      exact absurd h Bool.false_ne_true
    | cons c t =>
      rw [hexAtK_succ_cons c t rfl] at h
      rw [List.cons_append, hexAtK_succ_cons c (t ++ C) rfl]
      exact cenBRec_mono _ id ih h

theorem cenAscii_of {L C : List Char} {off d n w N : Nat} {F : Nat → Nat}
    (h : hexAtK (L ++ C) off d n w N F = true) (hl : L.length ≤ off + d * n * N) :
    ∀ c ∈ L, c.toNat < 128 := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  have hkC : k < (L ++ C).length := by simp; omega
  have := (hexAtK_ascii h k (by omega)).2
  rwa [getElem!_pos (L ++ C) k hkC, List.getElem_append_left hk] at this

theorem cenLink : cenPreK 91520 SuzCenTA0.chars SuzCenT.chars 0
    (fun s => cenPreK 840 SuzCenTB0.chars s 0 (fun s => cenPreK 91520 SuzCenTA1.chars s 0
    (fun s => cenPreK 840 SuzCenTB1.chars s 0 (fun s => cenPreK 91520 SuzCenTA2.chars s 0
    (fun s => cenPreK 840 SuzCenTB2.chars s 0 (fun s => cenPreK 91520 SuzCenTA3.chars s 0
    (fun s => cenPreK 840 SuzCenTB3.chars s 0 (fun s => cenPreK 91520 SuzCenTA4.chars s 0
    (fun s => cenPreK 840 SuzCenTB4.chars s 0 (fun s => cenPreK 91520 SuzCenTA5.chars s 0
    (fun s => cenPreK 840 SuzCenTB5.chars s 0 (fun s => cenPreK 91520 SuzCenTA6.chars s 0
    (fun s => cenPreK 840 SuzCenTB6.chars s 0 (fun s => cenPreK 91520 SuzCenTA7.chars s 0
    (fun s => cenPreK 840 SuzCenTB7.chars s 0 (fun s => cenPreK 91520 SuzCenTA8.chars s 0
    (fun s => cenPreK 841 SuzCenTB8.chars s 0
    (fun s => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) s)))))))))))))))))) =
    true := by
  quickRfl

theorem cenSplit : SuzCenT.chars = cenPieces.flatten ∧
    ∀ k (hk : k < 17), (cenPieces[k]'(by simp [cenPieces]; omega)).length = cenPL k := by
  obtain ⟨l0, s, h, h1⟩ := cenPreK_sound cenLink
  obtain ⟨l1, s, rfl, h2⟩ := cenPreK_sound h1
  obtain ⟨l2, s, rfl, h3⟩ := cenPreK_sound h2
  obtain ⟨l3, s, rfl, h4⟩ := cenPreK_sound h3
  obtain ⟨l4, s, rfl, h5⟩ := cenPreK_sound h4
  obtain ⟨l5, s, rfl, h6⟩ := cenPreK_sound h5
  obtain ⟨l6, s, rfl, h7⟩ := cenPreK_sound h6
  obtain ⟨l7, s, rfl, h8⟩ := cenPreK_sound h7
  obtain ⟨l8, s, rfl, h9⟩ := cenPreK_sound h8
  obtain ⟨l9, s, rfl, h10⟩ := cenPreK_sound h9
  obtain ⟨l10, s, rfl, h11⟩ := cenPreK_sound h10
  obtain ⟨l11, s, rfl, h12⟩ := cenPreK_sound h11
  obtain ⟨l12, s, rfl, h13⟩ := cenPreK_sound h12
  obtain ⟨l13, s, rfl, h14⟩ := cenPreK_sound h13
  obtain ⟨l14, s, rfl, h15⟩ := cenPreK_sound h14
  obtain ⟨l15, s, rfl, h16⟩ := cenPreK_sound h15
  obtain ⟨l16, s, rfl, h17⟩ := cenPreK_sound h16
  obtain ⟨-, s, rfl, h18⟩ := cenPreK_sound h17
  have z := fun {L : List Char} {n : Nat} (h : L.length + 0 = n) =>
    (Nat.add_zero L.length).symm.trans h
  refine ⟨?_, fun k hk => ?_⟩
  · cases s with
    | nil =>
      rw [h]
      simp only [cenPieces, List.flatten_cons, List.flatten_nil, List.append_nil]
    | cons _ _ => exact absurd h18 Bool.false_ne_true
  · interval_cases k
    exacts [z l0, z l1, z l2, z l3, z l4, z l5, z l6, z l7, z l8, z l9, z l10, z l11, z l12,
      z l13, z l14, z l15, z l16]

theorem cenChars_eq : SuzCenT.chars = cenPieces.flatten := cenSplit.1

@[expose] noncomputable def cenFullP (r : Nat) : Bool :=
  hexAtK (cenPieces.getD (2 * r) []) 0 4 32 15 715 (offF SuzCenR (Nat.mul 715 r))

@[expose] noncomputable def cenCompP (r : Nat) : Bool :=
  hexAtK (cenPieces.getD (2 * r + 1) []) 0 3 280 9 1 (offF SuzCenC r)

theorem full0 : cenFullP 0 = true := by quickRfl
theorem full1 : cenFullP 1 = true := by quickRfl
theorem full2 : cenFullP 2 = true := by quickRfl
theorem full3 : cenFullP 3 = true := by quickRfl
theorem full4 : cenFullP 4 = true := by quickRfl
theorem full5 : cenFullP 5 = true := by quickRfl
theorem full6 : cenFullP 6 = true := by quickRfl
theorem full7 : cenFullP 7 = true := by quickRfl
theorem full8 : cenFullP 8 = true := by quickRfl

theorem comp0 : cenCompP 0 = true := by quickRfl
theorem comp1 : cenCompP 1 = true := by quickRfl
theorem comp2 : cenCompP 2 = true := by quickRfl
theorem comp3 : cenCompP 3 = true := by quickRfl
theorem comp4 : cenCompP 4 = true := by quickRfl
theorem comp5 : cenCompP 5 = true := by quickRfl
theorem comp6 : cenCompP 6 = true := by quickRfl
theorem comp7 : cenCompP 7 = true := by quickRfl
theorem comp8 : cenCompP 8 = true := by quickRfl

theorem cenFullP_all {r : Nat} (hr : r < 9) : cenFullP r = true := by
  interval_cases r
  exacts [full0, full1, full2, full3, full4, full5, full6, full7, full8]

theorem cenCompP_all {r : Nat} (hr : r < 9) : cenCompP r = true := by
  interval_cases r
  exacts [comp0, comp1, comp2, comp3, comp4, comp5, comp6, comp7, comp8]

theorem cenDrop_eq {k : Nat} (hk : k < 18) :
    (cenPieces.drop k).flatten =
      cenPieces[k]'(by simp [cenPieces]; omega) ++ (cenPieces.drop (k + 1)).flatten := by
  rw [List.drop_eq_getElem_cons (by simp [cenPieces]; omega), List.flatten_cons]

theorem cenGetD_eq {k : Nat} (hk : k < 18) :
    cenPieces.getD k [] = cenPieces[k]'(by simp [cenPieces]; omega) := by
  have hl : k < cenPieces.length := by simp [cenPieces]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]

theorem cenLen {k : Nat} (hk : k < 17) :
    (cenPieces[k]'(by simp [cenPieces]; omega)).length = cenPL k :=
  cenSplit.2 k hk

theorem cenPiece_ext {r off d n w N : Nat} {F : Nat → Nat} (hr : r < 18)
    (h : hexAtK (cenPieces.getD r []) off d n w N F = true) :
    hexAtK (cenPieces.drop r).flatten off d n w N F = true := by
  rw [cenGetD_eq hr] at h
  rw [cenDrop_eq hr]
  exact hexAtK_append h

theorem cenAsciiAt {k : Nat} (hk : k < 17) :
    ∀ c ∈ cenPieces[k]'(by simp [cenPieces]; omega), c.toNat < 128 := by
  obtain ⟨r, rfl | rfl⟩ : ∃ r, k = 2 * r ∨ k = 2 * r + 1 := ⟨k / 2, by omega⟩
  · have h := cenFullP_all (r := r) (by omega)
    rw [cenFullP, cenGetD_eq (by omega)] at h
    refine cenAscii_of (C := []) (off := 0) (d := 4) (n := 32) (w := 15) (N := 715)
      (F := offF SuzCenR (Nat.mul 715 r)) (by rwa [List.append_nil]) ?_
    rw [cenLen hk, cenPL]
    omega
  · have h := cenCompP_all (r := r) (by omega)
    rw [cenCompP, cenGetD_eq (by omega)] at h
    refine cenAscii_of (C := []) (off := 0) (d := 3) (n := 280) (w := 9) (N := 1)
      (F := offF SuzCenC r) (by rwa [List.append_nil]) ?_
    rw [cenLen hk, cenPL]
    omega

theorem cenPre_len : ∀ k, k ≤ 17 →
    (cenPieces.take k).flatten.length = 92360 * (k / 2) + 91520 * (k % 2) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    rw [List.take_add_one,List.flatten_append, List.length_append, ih (by omega),
      List.getElem?_eq_getElem (by simp [cenPieces]; omega), Option.toList_some,
      List.flatten_cons, List.flatten_nil, List.append_nil, cenLen (by omega), cenPL]
    omega

theorem cenLift {k off o d n w N : Nat} {F : Nat → Nat} (hk : k < 18)
    (ho : 92360 * (k / 2) + 91520 * (k % 2) + off = o)
    (h : hexAtK (cenPieces.drop k).flatten off d n w N F = true) :
    hexAtK SuzCenT.chars o d n w N F = true := by
  have hpre : ∀ L ∈ cenPieces.take k, ∀ c ∈ L, c.toNat < 128 := by
    intro L hL
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
    have hj' : j < k := by simp [cenPieces] at hj; omega
    simp only [List.getElem_take]
    exact cenAsciiAt (by omega)
  rw [← ho, cenChars_eq, ← List.take_append_drop k cenPieces, List.flatten_append,
    ← cenPre_len k (by omega)]
  refine hexAtK_skipAscii (fun c hc => ?_) h
  obtain ⟨L, hL, hcL⟩ := List.mem_flatten.mp hc
  exact hpre L hL c hcL

theorem fullB_all {r : Nat} (hr : r < 9) : fullB r = true :=
  cenLift (k := 2 * r) (by omega) (by simp only [Nat.mul_eq]; omega)
    (cenPiece_ext (by omega) (cenFullP_all hr))

theorem compB_all {r : Nat} (hr : r < 9) : compB r = true :=
  cenLift (k := 2 * r + 1) (by omega) (by simp only [Nat.mul_eq, Nat.add_eq]; omega)
    (cenPiece_ext (by omega) (cenCompP_all hr))

@[expose] noncomputable def cenPermK (R n w m : Nat) (F : Nat → Nat) (o : Nat) (G : Nat → Nat)
    (o' : Nat) : Bool :=
  allN R (fun r => strictB (F (Nat.add o r)) (fun row => allN (nat_lit 32) (fun t =>
    strictB (fld(row, Nat.mul w t, m)) (fun v =>
      bAnd(Nat.blt v n, Nat.beq (rg w m G o' v) (Nat.add (Nat.mul (nat_lit 32) r) t))))))

theorem cenPermK_rpermK {R n w m o o' : Nat} {F G : Nat → Nat} (hn : n = 32 * R)
    (h : cenPermK R n w m F o G o' = true) : rpermK n w m F o G o' = true := by
  unfold rpermK
  apply CFSG.KS.PackFld.allN_of_forall
  intro i hi
  have h1 := CFSG.KS.allN_spec h (i / 32) (by omega)
  rw [CFSG.KS.PackFld.strictB_eqP] at h1
  have h2 := CFSG.KS.allN_spec h1 (i % 32) (Nat.mod_lt i (by omega))
  have e5 : Nat.shiftRight i 5 = i / 32 := Nat.shiftRight_eq_div_pow i 5
  have e31 : Nat.land i 31 = i % 32 := Nat.and_two_pow_sub_one_eq_mod i 5
  have ei : Nat.add (Nat.mul 32 (i / 32)) (i % 32) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [ei] at h2
  rw [rg, e5, e31]
  exact h2

theorem cenPerms : allN 9 (fun r =>
    cenPermK 715 22880 15 (mask 15) SuzCenR (Nat.mul 715 r) SuzCenRI (Nat.mul 715 r)) = true := by
  quickRfl

theorem full_perms : allN 9 (fun r =>
    rpermK 22880 15 (mask 15) SuzCenR (Nat.mul 715 r) SuzCenRI (Nat.mul 715 r)) = true :=
  CFSG.KS.PackFld.allN_of_forall fun r hr => cenPermK_rpermK rfl (CFSG.KS.allN_spec cenPerms r hr)

theorem comp_perms : allN 9 (fun r =>
    invEqK 280 9 (mask 9) (280 * 9) (SuzCenC r) (SuzCenCI r)) = true := by
  quickRfl

theorem centerFull_eq {r : Nat} (hr : r < 9) :
    centerFull r = rowArr 22880 15 SuzCenR (715 * r) := by
  have h := hexTable_rowsAt (R := 715) (e := 23090 * r) (fullB_all hr)
  rw [← SuzCenT.eq] at h
  exact h

theorem centerCompact_eq {r : Nat} (hr : r < 9) : centerCompact r = unpack 280 9 (SuzCenC r) := by
  have h := hexAt_unpack (compB_all hr) (j := 0) (by decide)
  rw [← SuzCenT.eq] at h
  refine Eq.trans ?_ h
  apply Array.ext
  · simp [centerCompact]
  · intro x _ _
    simp only [centerCompact, Array.getElem_ofFn]
    have ex : 92360 * r + 91520 + 3 * x = Nat.add (Nat.mul 92360 r) 91520 + 3 * (280 * 0 + x) := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rw [ex]

end CertificateChecks.KernelSpor.OddCore

end
