module

public import Certificates.Kernel.SporSch.Ly.R3EData
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyR3E

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF

local notation "U" X:max => unpackL 111 12 1332 X

theorem vUGk {k : Nat} (hk : k < 6) : vld (LySy.UG k) = true := allN_spec LySy.vUG k hk

theorem vEi {i : Nat} (hi : i < 256) : vld (LySy.E i) = true := by
  rcases Nat.lt_or_ge i 64 with a | a
  · simpa [Nat.add_eq] using allBlk_spec LySy.vE0 i a
  rcases Nat.lt_or_ge i 128 with b | b
  · simpa [Nat.add_eq, Nat.add_sub_cancel' a] using allBlk_spec LySy.vE1 (i - 64) (by omega)
  rcases Nat.lt_or_ge i 192 with c | c
  · simpa [Nat.add_eq, Nat.add_sub_cancel' b] using allBlk_spec LySy.vE2 (i - 128) (by omega)
  · simpa [Nat.add_eq, Nat.add_sub_cancel' c] using allBlk_spec LySy.vE3 (i - 192) (by omega)

theorem us_get (k : Nat) (hk : k < 6) : (sylowGens (cStarArr (U B4)))[k]! = U (LySy.UG k) := by
  rcases Nat.lt_or_ge k 5 with h | h
  · rw [sylow_get h, (word_of csCF csCI (fun i => (vCFx le_rfl i).1)
      (fun i => (vCFx le_rfl i).2) _).1, Nat.eq_of_beq_eq_true (allN_spec LySy.ugw k h)]
  · have : k = 5 := by omega
    subst this
    have e : (sylowGens (cStarArr (U B4)))[5]! = matA := by
      unfold sylowGens
      rw [getElem!_pos _ 5 (by simp)]
      simp [Array.getElem_push]
    rw [e, matA_eq, Nat.eq_of_beq_eq_true LySy.ug5]

theorem us_size : (sylowGens (cStarArr (U B4))).size = 6 := by simp [sylowGens]

theorem pts_eq : (sylowBFS (sylowGens (cStarArr (U B4))) 256).1 =
    Array.ofFn (n := 256) fun i => U (LySy.E i.val) := by
  have h := runB_sound (kg := 6) (c := 256) (cap := 256) (nS := 32) (Hh := 8) (UG := LySy.UG)
    (E := LySy.E) (W := LySy.W) (SO := LySy.ST) (SOI := LySy.SIT) (C := LySy.C) consts
    (fun k hk => hv (vUGk hk)) (fun i hi => hv (vEi hi)) (Nat.eq_of_beq_eq_true LySy.e0)
    (by decide) (fun i hi => allN_spec LySy.srt i hi) rfl (Nat.eq_of_beq_eq_true LySy.c0)
    (Nat.eq_of_beq_eq_true LySy.cN) LySy.hrun ⟨us_size, us_get⟩
  exact h

theorem get_ofFn {n i : Nat} {f : Fin n → Mat} (hi : i < n) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem vF : vld (LySy.E 113) = true := vEi (by omega)

theorem cword (w : List Int) :
    cWordM (cStarArr (U B4)) w = U (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE w) ∧
      vld (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE w) = true :=
  word_of csCF csCI (fun i => (vCFx le_rfl i).1) (fun i => (vCFx le_rfl i).2) w

theorem commW_of {w : List Int} (h : LySy.commW w = true) :
    (let md := cWordM (cStarArr (U B4)) w;
      mulM 5 111 md (U (LySy.E 113)) == mulM 5 111 (U (LySy.E 113)) md) = true := by
  simp only []
  obtain ⟨e, v⟩ := cword w
  rw [e, mulE v vF, mulE vF v, beqE (mulV v vF) (mulV vF v)]
  unfold LySy.commW at h
  rwa [CFSG.KS.Raw.strictB_eq] at h

theorem mg_eq : r3eGM (r3eHM (U B4)) (U (LySy.E 113)) = U LySy.MG2 := by
  obtain ⟨_, vh, _⟩ := vMs
  rw [hm_eq]
  unfold r3eGM
  rw [mulE vh vF, matA_eq, mulE vA vh, (powM_eq consts (hv (mulV vh vF)) 7).1,
    (powM_eq consts (hv (mulV vA vh)) 4).1,
    mulE (powM_eq consts (hv (mulV vh vF)) 7).2 (powM_eq consts (hv (mulV vA vh)) 4).2]
  rfl

theorem p18 {D : Nat} (hD : vld D = true) :
    r3eP18 (U (CF 3)) (U D) (U LySy.MG2) =
      U (powR 5 12 1332 111 8 L H CM RM ONE (mul (mul (CF 3) D) LySy.MG2) 18) ∧
    vld (powR 5 12 1332 111 8 L H CM RM ONE (mul (mul (CF 3) D) LySy.MG2) 18) = true := by
  have v3 := (vCFi (i := 3) (by omega)).1
  unfold r3eP18
  rw [mulE v3 hD, mulE (mulV v3 hD) LySy.vMG2]
  exact powM_eq consts (hv (mulV (mulV v3 hD) LySy.vMG2)) 18

theorem nb {X Y : Nat} (h : Bool.not (Nat.beq X Y) = true) : Nat.beq X Y = false := by
  simpa using h

theorem facts : r3eCertificate () = true := by
  unfold r3eCertificate
  simp only []
  rw [b4_eq]
  unfold r3eWithStar r3eWithGens r3eChecks
  simp only []
  have hc3 : (pairAt (cStarArr (U B4)) 3).1 = U (CF 3) := by
    rw [csCF]
    rfl
  rw [pts_eq, get_ofFn (i := 113) (by omega), us_get 2 (by omega), us_get 1 (by omega), hc3]
  simp only []
  rw [mg_eq]
  have v1 := vUGk (k := 1) (by omega)
  have v2 := vUGk (k := 2) (by omega)
  have hP1 := p18 vOne
  have hPA := p18 vA
  have hPF := p18 vF
  have hPAF := p18 (mulV vA vF)
  rw [← idE] at hP1
  rw [← matA_eq] at hPA
  rw [← mulE vA vF, ← matA_eq] at hPAF
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [mulE v2 v1, mulE (mulV v2 v1) v2, mulE (mulV (mulV v2 v1) v2) v1,
      beqE (mulV (mulV (mulV v2 v1) v2) v1) vF]
    exact LySy.a1
  · rw [mulE vF vF, idE, beqE (mulV vF vF) vOne]
    exact LySy.a2
  · rw [idE, diffMod5_eq consts (hv vF) (hv vOne), nb LySy.a3]
    rfl
  · rw [matA_eq, diffMod5_eq consts (hv vF) (hv vA), nb LySy.a4]
    rfl
  · rw [matA_eq, mulE vA vF, mulE vF vA, beqE (mulV vA vF) (mulV vF vA)]
    exact LySy.a5
  · rw [matA_eq, mulE LySy.vMG2 vA, mulE vF LySy.vMG2, beqE (mulV LySy.vMG2 vA) (mulV vF LySy.vMG2)]
    exact LySy.a6
  · rw [List.all_eq_true]
    intro w hw
    simp only [r3eWordsN, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact commW_of LySy.w0
    · exact commW_of LySy.w1
    · exact commW_of LySy.w2
    · exact commW_of LySy.w3
    · exact commW_of LySy.w4
    · exact commW_of LySy.w5
  · rw [hP1.1, idE, beqE hP1.2 vOne]
    exact LySy.p1
  · rw [hPA.1, idE, diffMod5_eq consts (hv hPA.2) (hv vOne), nb LySy.p2]
    rfl
  · rw [hPF.1, idE, diffMod5_eq consts (hv hPF.2) (hv vOne), nb LySy.p3]
    rfl
  · rw [hPAF.1, idE, beqE hPAF.2 vOne]
    exact LySy.p4

end CertificateChecks.KernelSporSch.LyR3E

end
