module

public import Certificates.Kernel.LocalComp.Weyl3184
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CertificateChecks.KernelLC.W3184

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelLC.Weyl (wBaseArr nilD)

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bindList_aux (n P : Nat) : ∀ (L : List Nat) (j0 : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
      (fun p _ ih j => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ j))
          (Nat.beq p (pg (nat_lit 8) (nat_lit 255) P j)))
        (Nat.blt p (nat_lit 240))) L j0 = true →
    j0 + L.length = n ∧ ∀ j < L.length, L[j]! < 240 ∧ L[j]! = pg 8 255 P (j0 + j)
  | [], j0, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | p :: L, j0, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨ih1, ih2⟩ := bindList_aux n P L (j0 + 1) h4
    refine ⟨by simp only [List.length_cons]; omega, fun j hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem!_cons_zero, Nat.add_zero]
      exact ⟨by simpa [Nat.blt_eq] using h1, Nat.eq_of_beq_eq_true h3⟩
    | succ j =>
      have := ih2 j (by simp only [List.length_cons] at hj; omega)
      simpa only [List.getElem!_cons_succ, Nat.add_succ, Nat.succ_add] using this

theorem bindList_spec {L : List Nat} {n P : Nat} (h : bindList L n P = true) :
    L.length = n ∧ ∀ j < n, L[j]! < 240 ∧ L[j]! = pg 8 255 P j := by
  obtain ⟨h1, h2⟩ := bindList_aux n P L 0 h
  refine ⟨by omega, fun j hj => ?_⟩
  simpa only [Nat.zero_add] using h2 j (by omega)

theorem map_get (L : List Nat) (f : Nat → Array Nat) (j : Nat) (hj : j < L.length) :
    (L.map f).toArray[j]! = f L[j]! := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [getElem!_pos L j hj]

theorem wS_get (j : Nat) (hj : j < 13) : wS[j]! = unpack 240 8 (W.S j) := by
  obtain ⟨hl, hs⟩ := bindList_spec kSG
  obtain ⟨hp, he⟩ := hs j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec kSGS j hj), ← he, ← E8.refl_eq _ hp]
  exact map_get _ _ j (by omega)

theorem reflS_get (j : Nat) (hj : j < 120) : reflS[j]! = unpack 240 8 (posT j) := by
  obtain ⟨hl, hs⟩ := bindList_spec kPOS
  obtain ⟨hp, he⟩ := hs j hj
  rw [posT, ← he, ← E8.refl_eq _ hp]
  exact map_get _ _ j (by omega)

theorem wS_size : wS.size = 13 := by
  simp only [wS, List.size_toArray, List.length_map, (bindList_spec kSG).1]

theorem binds : Binds 240 8 W.S 13 8 W.BP wS wBaseArr :=
  ⟨by norm_num, by norm_num, by norm_num, wS_size, wS_get, by decide, by decide⟩

theorem wWords_eq : wWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 13 13 nilD := by
  decide

theorem kRange : allN 240 (fun r => allN 240 (fun i => Nat.blt (pg 8 (mask 8) (E8.RT r) i) 240)) =
    true := by
  quickRfl

theorem wChain : wChainCheck = true := by
  have hc := rawChainK_sound (NS := 15) (CH := 16) (chunks := 4) binds W.head W.hl (by norm_num) W.hs
  rw [← wWords_eq] at hc
  have ho : rawOrbitSizes 240 wS wBaseArr = [240, 126, 60, 2, 24, 2, 2, 2] := by
    rw [rawOrbitSizesK_sound binds perm W.hl]
    decide
  have hs : ∀ r < 240, siftA 240 (rawLevels 240 wS wBaseArr) wBaseArr 0 (reflArr r) = true := by
    intro r hr
    obtain ⟨k1, k2⟩ := (bAnd_iff _ _).1 (allN_spec kSift r hr)
    exact siftK_soundR binds perm W.hl (E8.refl_eq r hr) (Nat.eq_of_beq_eq_true k1)
      (allN_spec kRange r hr) k2
  simp only [wChainCheck, Bool.and_eq_true, beq_iff_eq, allLt_iff]
  exact ⟨⟨hc, ho⟩, hs⟩

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  simp only [unpack]
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem reflCheck_ok : reflCheck = true := by
  have hR := E8.refl_eq
  have hN := E8.neg_eq
  have kr := allN_spec kRefl
  have kn := kNeg
  simp only [negFacts, bAnd_iff] at kn
  obtain ⟨kn1, kn2, kn3⟩ := kn
  have kn3 := allN_spec kn3
  simp only [reflCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  refine ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, fun r hr => ?_⟩
  · have k := kr r hr
    rw [strictB_eq] at k
    simp only [reflFactAt, negAt, witAt, bAnd_iff] at k
    obtain ⟨k1, k2, ⟨k3, k4⟩, k5, k6⟩ := k
    have hlt : pg 8 255 E8.NEG r < 240 := by simpa [Nat.blt_eq] using k3
    have hng : negArr[r]! = pg 8 255 E8.NEG r := by rw [hN, unpack_get hr]; rfl
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [hR r hr]
      exact (invEqK_sound (by exact k1)).2
    · rw [hR r hr, fixCntK_sound]
      exact Nat.eq_of_beq_eq_true k2
    · rw [hng]
      exact hlt
    · rw [hng, hR _ hlt, hR r hr, Nat.eq_of_beq_eq_true k4]
      exact eqK_sound (Nat.beq_refl _)
    · refine ⟨pg 8 255 WIT r, by simpa [Nat.blt_eq] using k5, ?_⟩
      rw [hR r hr, reflS_get _ (by simpa [Nat.blt_eq] using k5), ← Nat.eq_of_beq_eq_true k6]
      exact eqK_sound (Nat.beq_refl _)
  · rw [hN]; exact (invEqK_sound (by exact kn1)).2
  · rw [hN, fixCntK_sound]; exact Nat.eq_of_beq_eq_true kn2
  · rw [hN, hR r hr]
    exact commK_sound (by exact kn3 r hr)

end CertificateChecks.KernelLC.W3184

end
