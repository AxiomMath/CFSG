
module

public import CFSG.Monster.B.Fischer.Fi22CertInputs
public import Certificates.Kernel.Sporadic.Fi22.Cert3149K
public import Certificates.Kernel.Sporadic.Fi22.C3152
public import CFSG.Certificates.Kernel.Spor.HexAtSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3149

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.F3152 CFSG.KC.BM.Pkt CFSG.KS.Text
open CFSG.F3.Native CFSG.KS.F3L CFSG.KC.Misc.HexAt
open CFSG.Monster.B.Fischer CFSG.Monster.B.Fischer.Native

theorem utf8_size {cs : List Char} (h : ∀ c ∈ cs, c.toNat < 128) :
    (String.ofList cs).toUTF8.size = cs.length := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
    flatMap_ascii' cs h]
  change (List.toByteArray _).data.size = _
  rw [List.data_toByteArray, List.size_toArray, List.length_map]

theorem flat_len : ∀ L : List (Nat × Nat), (∀ p ∈ L, p.2 = 752) →
    (L.flatMap pieceBytes).length = 752 * L.length
  | [], _ => rfl
  | p :: L, h => by
    have hp : p.2 = 752 := h p List.mem_cons_self
    rw [List.flatMap_cons, List.length_append, flat_len L (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      List.length_cons]
    unfold pieceBytes
    rw [List.length_map, List.length_range, hp]
    ring

theorem line_bytes {S : V} {N : Nat} (h : lineOK S N = true) :
    (∀ m < 751, 40 ≤ (N >>> (8 * m)) % 256 ∧ (N >>> (8 * m)) % 256 < 121) ∧
      (N >>> (8 * 751)) % 256 = 10 := by
  obtain ⟨hS, -, hB⟩ := lineOK_parts h
  obtain ⟨h1, h2⟩ := bytesK_spec 751 N _ _ hB
  have hdisj := plOf_disj (upperOf_disj hS)
  refine ⟨fun m hm => ?_, by rw [h2]⟩
  rw [h1 m hm, tri4_eq, tri4_eq]
  simp only [Nat.testBit_shiftRight]
  have := toNat_disj (hdisj (4 * m + 0))
  have := toNat_disj (hdisj (4 * m + 1))
  have := toNat_disj (hdisj (4 * m + 2))
  have := toNat_disj (hdisj (4 * m + 3))
  omega

theorem linesOK_text {CH : List (Nat × Nat)} {n : Nat} {S : Nat → V} (hlen : CH.length = n)
    (hl : ∀ r < n, CH[r]? = some ((CH.getD r (0, 0)).1, 752) ∧
      lineOK (S r) (CH.getD r (0, 0)).1 = true) :
    linesOK (String.ofList (CFSG.KC.YModel.charsOf CH)).toUTF8 n = true := by
  have hmem : ∀ p ∈ CH, ∃ r < n, p = ((CH.getD r (0, 0)).1, 752) := by
    intro p hp
    obtain ⟨r, hr, e⟩ := List.getElem_of_mem hp
    refine ⟨r, by omega, ?_⟩
    have := (hl r (by omega)).1
    rw [List.getElem?_eq_getElem hr, e] at this
    exact Option.some.inj this
  have hw : ∀ p ∈ CH, p.2 = 752 := by
    intro p hp
    obtain ⟨r, _, rfl⟩ := hmem p hp
    rfl
  have hasc : ∀ c ∈ CFSG.KC.YModel.charsOf CH, c.toNat < 128 := by
    intro c hc
    rw [charsOf_eq, bytesOf_eq] at hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨r, hr, rfl⟩ := hmem p hp
    unfold pieceBytes at hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    rw [chAt_eq]
    have := lineOK_code (hl r hr).2 (List.mem_range.1 hm)
    rw [ofNat_toNat_ascii _ this]
    exact this
  have hsz : (String.ofList (CFSG.KC.YModel.charsOf CH)).toUTF8.size = 752 * n := by
    rw [utf8_size hasc, charsOf_eq, bytesOf_eq, List.length_map, flat_len CH hw, hlen]
  unfold linesOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨hsz, CFSG.Monster.B.Co2.allLt_iff.2 fun r hr => ?_⟩
  obtain ⟨hb, h10⟩ := line_bytes (hl r hr).2
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, CFSG.Monster.B.Co2.allLt_iff.2 fun m hm => ?_⟩
  · apply UInt8.toNat_inj.1
    rw [text_get hlen hl hr (by norm_num), h10]
    rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [text_get hlen hl hr (by omega)]
    exact hb m hm

theorem forms_lines : linesOK fi22FormsBytes 3510 = true := by
  unfold fi22FormsBytes
  rw [F3152.T.eq]
  exact linesOK_text F3152.ch_len (fun r hr => F3152.ch_get hr)

theorem inv_lines : linesOK fi22InvFormBytes 1 = true := by
  unfold fi22InvFormBytes
  rw [F3152.TI.eq]
  exact linesOK_text F3152.ti_get.1 F3152.ti_get.2

theorem hexAt_eq (b : ByteArray) (o : Nat) : ∀ w,
    CFSG.Monster.B.Max2.Native.hexAt b o w = CFSG.Monster.B.Co2.Native.hexAt b o w
  | 0 => rfl
  | w + 1 => by
    rw [CFSG.Monster.B.Max2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexAt, hexAt_eq b o w]
    rfl

theorem hexAt3 (b : ByteArray) (o : Nat) : CFSG.Monster.B.Max2.Native.hexAt b o 3 =
    ((0 * 16 + CFSG.Monster.B.Max2.Native.hexAt b o 1) * 16 +
      CFSG.Monster.B.Max2.Native.hexAt b (o + 1) 1) * 16 +
      CFSG.Monster.B.Max2.Native.hexAt b (o + 2) 1 := by
  simp [CFSG.Monster.B.Max2.Native.hexAt, Nat.add_assoc]

theorem so_bytes : fi22StabOrbitsBytes = (String.ofList SOC).toUTF8 := by
  unfold fi22StabOrbitsBytes
  rw [SOC_eq]

theorem mg_bytes : fi22MergeBytes = (String.ofList MGC).toUTF8 := by
  unfold fi22MergeBytes
  rw [MGC_eq]

theorem G_eq {k : Nat} (hk : k < 3510) :
    CFSG.Monster.B.Max2.Native.hexAt fi22StabOrbitsBytes (3 * k) 3 = G k := by
  have h := hexAtK_sound bindSO 0 (by norm_num) k hk
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at h
  rw [so_bytes, hexAt_eq, h]
  rfl

theorem D_eq {i : Nat} (hi : i < 49112) :
    CFSG.Monster.B.Max2.Native.hexAt fi22MergeBytes i 1 = D i := by
  have h := hexAtK_sound bindMG 0 (by norm_num) i hi
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.one_mul] at h
  rw [mg_bytes, hexAt_eq, h]
  rfl

theorem D3_eq {i : Nat} (hi : i + 2 < 49112) :
    CFSG.Monster.B.Max2.Native.hexAt fi22MergeBytes i 3 = D3 i := by
  rw [hexAt3, D_eq (by omega), D_eq (by omega), D_eq (by omega)]
  rfl

theorem ascii_of {cs : List Char} (h : asciiK cs = true) : ∀ c ∈ cs, c.toNat < 128 :=
  asciiK_spec h

theorem start_le : ∀ t < 3, fi22StabOrbitStart t + fi22StabOrbitSizes.getD t 0 ≤ 3510 := by
  decide

theorem pw_range {f : Nat → Nat} {L : Nat} (h : ∀ k, k + 1 < L → f k < f (k + 1)) :
    (List.range L).Pairwise (fun a b => f a < f b) := by
  have mono : ∀ b, b < L → ∀ a < b, f a < f b := by
    intro b
    induction b with
    | zero => intro _ a ha; omega
    | succ b ih =>
      intro hb a ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h' | rfl
      · exact lt_trans (ih (by omega) a h') (h b hb)
      · exact h a hb
  exact (List.pairwise_lt_range (n := L)).imp_of_mem fun _ hb hab => mono _ (List.mem_range.1 hb) _ hab

theorem orbit_pw {s L : Nat} (hs : s + L ≤ 3510)
    (h : ∀ k, k + 1 < L → G (s + k) < G (s + k + 1)) :
    ((List.range L).map fun k =>
      CFSG.Monster.B.Max2.Native.hexAt fi22StabOrbitsBytes (3 * (s + k)) 3).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  refine pw_range fun k hk => ?_
  rw [G_eq (by omega), G_eq (by omega)]
  exact h k hk

open Certificates in
open CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Fischer in
theorem c3149 : linesOK fi22FormsBytes 3510 = true ∧ linesOK fi22InvFormBytes 1 = true ∧
      fi22StabOrbitsBytes.size = 3 * 3510 ∧ fi22MergeBytes.size = 7 * 2 * fi22MergeLength ∧
      (∀ t < 3, ∀ x ∈ fi22StabOrbit t, x < 3510) ∧
      (∀ t < 3, (fi22StabOrbit t).Pairwise (· < ·)) ∧
      ((List.range 3).map fun t => (fi22StabOrbit t).length) = [1, 2816, 693] ∧
      (fi22Merges.map fun m => (m.1 : Nat)) = [1, 11] ∧
      (fi22Merges.map fun m => m.2.length) = [3508, 3508] ∧
      (∀ m < 2, ∀ k < fi22MergeLength, (fi22MergeRaw m k).1 < 2 ∧ (fi22MergeRaw m k).2.1 < 3510 ∧
        (fi22MergeRaw m k).2.2 < 3510) := by
  have aSO := ascii_of asciiSO
  have aMG := ascii_of asciiMG
  have lSO : SOC.length = 10530 := Nat.eq_of_beq_eq_true lenSO
  have lMG : MGC.length = 49112 := Nat.eq_of_beq_eq_true lenMG
  refine ⟨forms_lines, inv_lines, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [so_bytes, utf8_size aSO, lSO]
  · rw [mg_bytes, utf8_size aMG, lMG]
    rfl
  · intro t ht x hx
    unfold fi22StabOrbit at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hk' := List.mem_range.1 hk
    have hs := start_le t ht
    rw [G_eq (by omega)]
    exact Nat.blt_eq.mp (allN_spec ptsLt _ (by omega))
  · intro t ht
    unfold fi22StabOrbit
    interval_cases t
    · exact orbit_pw (s := fi22StabOrbitStart 0) (L := 1) (by decide) fun k hk => by omega
    · refine orbit_pw (s := fi22StabOrbitStart 1) (L := 2816) (by decide) fun k hk => ?_
      have e : fi22StabOrbitStart 1 = 1 := by decide
      rw [e]
      exact Nat.blt_eq.mp (allN_spec inc1 k (by omega))
    · refine orbit_pw (s := fi22StabOrbitStart 2) (L := 693) (by decide) fun k hk => ?_
      have e : fi22StabOrbitStart 2 = 2817 := by decide
      rw [e]
      exact Nat.blt_eq.mp (allN_spec inc2 k (by omega))
  · simp only [fi22StabOrbit, List.length_map, List.length_range]
    decide
  · simp [fi22Merges, fi22Pt, fi22MergeReps]
  · simp [fi22Merges, fi22MergeList, fi22MergeLength]
  · intro m hm k hk
    have hk' : k < 3508 := hk
    have hj : 3508 * m + k < 7016 := by omega
    have h := allN_spec merges _ hj
    unfold mgOK at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    have e : fi22MergeLength = 3508 := rfl
    simp only [fi22MergeRaw, e]
    refine ⟨?_, ?_, ?_⟩
    · rw [D_eq (by omega)]
      have := Nat.blt_eq.mp h1
      omega
    · rw [D3_eq (by omega)]
      exact Nat.blt_eq.mp h2
    · rw [show 7 * (3508 * m + k) + 4 = 7 * (3508 * m + k) + 4 from rfl, D3_eq (by omega)]
      exact Nat.blt_eq.mp h3

end CertificateChecks.KernelSpor.F3149

end
