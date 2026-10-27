module

public import Certificates.Kernel.SmithD6UwB.Checks
public import CFSG.Certificates.Kernel.SmithD6UwBSound
public import Certificates.Kernel.SmithD6Wt.Facts

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6UwB

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.KD.SmithD6
  CertificateChecks.SmithD6Wt

theorem ubNth_eq : ∀ (cs : List (List (Nat × Nat × Nat))) (c : Nat), ubNth cs c = cs.getD c []
  | [], _ => by
    change [] = _
    simp
  | _ :: _, 0 => rfl
  | _ :: cs, c + 1 => by
    change ubNth cs c = _
    rw [ubNth_eq cs c]
    simp

theorem ubRec_all : ∀ p (hp : p < J.wt64C.flatten.length),
    ∃ r, (∃ ch ∈ JB.bRC, r ∈ ch) ∧ ubRecOK p J.wt64C.flatten[p] r = true := by
  have h64 : J.wt64C.length = 37 := by rw [← lenC_eq, wt64C_lenC]
  intro p hp
  obtain ⟨l, hl, hs⟩ := List.mem_flatten.1 (List.getElem_mem hp)
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hl
  obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
  have hc37 : c < 37 := by rw [h64] at hc; exact hc
  obtain ⟨hf, -, -⟩ := chunkOK_sound hc (wt64Chunks_ok c hc37)
  have hpj : p = 2048 * c + j := by
    have h1 := hf j hj
    rw [hjs, wt64_facts.2.2.1 p hp] at h1
    omega
  have hO := ubChunks_ok c hc37
  rw [ubOK, nthC_eq, ubNth_eq, getD_eq hc] at hO
  obtain ⟨hlen, hrec⟩ := ubGo_sound _ _ _ hO
  have hrl : c < JB.bRC.length := by rw [bRC_length]; exact hc37
  rw [getD_eq hrl] at hlen hrec
  refine ⟨(JB.bRC[c])[j]'(by rw [hlen]; exact hj),
    ⟨JB.bRC[c], List.getElem_mem hrl, List.getElem_mem _⟩, ?_⟩
  have := hrec j hj (by rw [hlen]; exact hj)
  rw [← hjs, hpj]
  exact this

theorem ubK_eq (p : Nat) (hp : p < J.wt64C.flatten.length) :
    pkGet JB.bK 2 p = ubKOf J.wt64C.flatten[p] := by
  obtain ⟨r, -, hr⟩ := ubRec_all p hp
  exact (ubRecOK_sound hr).1

theorem ubFirst (p : Nat) (hp : p < J.wt64C.flatten.length) (hk : pkGet JB.bK 2 p ≠ 0) :
    ubRep (pkGet JB.bK 2 p) ≤ p := by
  obtain ⟨r, -, hr⟩ := ubRec_all p hp
  exact ((ubRecOK_sound hr).2 hk).1

def ubStep (a b : Nat) : Prop :=
  ∃ g < 30, pkGet JB.bK 2 a = pkGet JB.bK 2 b ∧ ∃ (ha : a < J.wt64C.flatten.length)
    (hb : b < J.wt64C.flatten.length),
    liftT (JU.uwT.getD (15 + g) []) J.wt64C.flatten[a] = J.wt64C.flatten[b]

theorem ubReach : ∀ v < J.wt64C.flatten.length, pkGet JB.bK 2 v ≠ 0 →
    Relation.ReflTransGen ubStep (ubRep (pkGet JB.bK 2 v)) v := by
  suffices H : ∀ n, ∀ v < J.wt64C.flatten.length, pkGet JB.bK 2 v ≠ 0 → pkGet JB.bD 5 v ≤ n →
      Relation.ReflTransGen ubStep (ubRep (pkGet JB.bK 2 v)) v from
    fun v hv hk => H _ v hv hk le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv hk hd
    obtain ⟨r, -, hr⟩ := ubRec_all v hv
    have := ((ubRecOK_sound hr).2 hk).2.1
    omega
  | succ n ih =>
    intro v hv hk hd
    obtain ⟨r, -, hr⟩ := ubRec_all v hv
    obtain ⟨-, hpos, hroot, hstep, -⟩ := (ubRecOK_sound hr).2 hk
    by_cases h1 : pkGet JB.bD 5 v = 1
    · rw [← hroot h1]
    · obtain ⟨hg, hl, p, hfind, -, hdp, hkp⟩ := hstep h1
      obtain ⟨hp, hpx⟩ := wt64_facts.2.2.2 r.2.1 p hfind
      have ihp := ih p hp (by rw [hkp]; exact hk) (by omega)
      rw [hkp] at ihp
      refine Relation.ReflTransGen.tail ihp ⟨r.1, hg, hkp, hp, hv, ?_⟩
      rw [hpx, hl]

theorem ubWit : ∀ v (hv : v < J.wt64C.flatten.length), pkGet JB.bK 2 v = 1 →
    ∃ k, lineTree.memB k = true ∧ k / 4096 < k % 4096 ∧ k % 4096 < (k / 4096 ^^^ k % 4096) ∧
      (k / 4096 ^^^ k % 4096) < 4096 ∧ k / 4096 &&& 63 = 0 ∧ k % 4096 &&& 63 = 0 ∧
      (ubTop ^^^ rhoK (k / 4096) (rhoK (k % 4096) ubTop)) = J.wt64C.flatten[v] := by
  intro v hv hk
  obtain ⟨r, ⟨ch, hch, hr⟩, hrec⟩ := ubRec_all v hv
  have hw := ubWitK_sound (((ubRecOK_sound hrec).2 (by rw [hk]; decide)).2.2.2.2 hk)
  refine ⟨r.2.2, ?_, hw⟩
  rcases ubKeysOK_sound ubKeysOK_ok ch hch r hr with h0 | h0
  · have := hw.1
    rw [h0] at this
    exact absurd this (by decide)
  · exact h0

theorem ubE0 : ∃ h : JB.bE0 < J.wt64C.flatten.length, J.wt64C.flatten[JB.bE0] = ubTop := by
  have h := ubHeadK_ok
  unfold ubHeadK at h
  simp only [Bool.and_eq_true] at h
  exact wt64_facts.2.2.2 ubTop JB.bE0 (Nat.eq_of_beq_eq_true h.1.1.1)

theorem ubLevi : ∀ g < 30, liftT (JU.uwT.getD (15 + g) []) ubTop = ubTop := by
  have h := ubHeadK_ok
  unfold ubHeadK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.1.2

theorem ubReps : JB.bReps.length = 3 ∧ ∀ c ∈ [1, 2, 3], ubRep c < 75735 ∧ pkGet JB.bK 2 (ubRep c) = c := by
  have h := ubHeadK_ok
  unfold ubHeadK at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

end CertificateChecks.SmithD6UwB

end
