module

public import Certificates.Kernel.SuzPump.Pair
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Spor.RebuildSound
public import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzPump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Solomon.Coordinator.SuzPump CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hw : szOK 1782 11 = true := by decide +kernel

theorem hbl : ∀ t < 6, smallBaseNat.toArray[t]! < 1782 :=
  Orb.base_lt_of_levels Suz2306.binds SuzC.hl

theorem reb_succ (B : Nat → Nat) (j : Nat) :
    rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B (j + 1) =
      rebStep 1782 11 SuzC.LR SuzC.TR SuzC.TRI B (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B j) j := by
  simp [rebK, List.range_succ, List.foldl_append]

theorem reb_ok (B : Nat → Nat) (h : (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B 6).2.2 = true) :
    ∀ j < 6, B j < 1782 ∧ rpos 11 (mask 11) (1782 * 11) (SuzC.LR j)
      (pg 11 (mask 11) (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B j).2.1 (B j)) < rcnt (SuzC.LR j) := by
  have down : ∀ d, d ≤ 6 → (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI B (6 - d)).2.2 = true := by
    intro d
    induction d with
    | zero => intro _; exact h
    | succ d ih =>
      intro hd
      have h' := ih (by omega)
      rw [show 6 - d = (6 - (d + 1)) + 1 by omega, reb_succ] at h'
      unfold rebStep at h'
      simp only [Bool.and_eq_true] at h'
      exact h'.1.1
  intro j hj
  have h' := down (5 - j) (by omega)
  rw [show 6 - (5 - j) = j + 1 by omega, reb_succ] at h'
  unfold rebStep at h'
  simp only [Bool.and_eq_true, Nat.blt_eq] at h'
  exact ⟨h'.1.2, h'.2⟩

theorem rebuild_eq {beta : Array Nat} (h : (reb beta).2.2 = true) :
    rebuild (levels ()) beta = unpack 1782 11 (reb beta).1 := by
  have hok := reb_ok _ h
  have key := CFSG.KS.BfsReplay.forIn_range'_yield 6 0 (idA 1782, idA 1782)
    (fun i (s : Array Nat × Array Nat) =>
      (pure (ForInStep.yield (compA 1782 s.1 (levels ())[i]!.tr[(levels ())[i]!.pos[s.2[beta[i]!]!]!]!,
        compA 1782 (levels ())[i]!.trInv[(levels ())[i]!.pos[s.2[beta[i]!]!]!]! s.2)) :
          Id (ForInStep (Array Nat × Array Nat))))
    (fun j s => Orb.RebSt 1782 11 s.1 s.2
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => beta[l]!) j).1
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => beta[l]!) j).2.1)
    (fun j hj s hs => by
      refine ⟨_, rfl, ?_⟩
      rw [Nat.zero_add, reb_succ]
      obtain ⟨hb, hk⟩ := hok j hj
      obtain ⟨A, hT⟩ := Orb.agree_levelK Suz2306.binds Suz2306.perm hbl hj (SuzC.hl j hj)
      exact (Orb.rebStep_spec (by norm_num) A hT hs hb hk).2)
    (Orb.rebSt_init (by norm_num) (by norm_num))
  obtain ⟨hs, -, γ, ha, -, hA, -⟩ := key
  unfold rebuild
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  exact Orb.rep_eq_unpack hs ha hA

theorem hX : rebuild (levels ()) xAβ = unpack 1782 11 XA := rebuild_eq rbX

theorem hng : E.ng = 2 := Nat.eq_of_beq_eq_true n0.2

theorem hN : E.N = 405 := Nat.eq_of_beq_eq_true n0.1

theorem hG : ∀ k < 2, pairGs[k]! = unpack 1782 11 (E.G k) := by
  intro k hk
  interval_cases k
  · change rebuild (levels ()) h1β = _
    rw [rebuild_eq rb1.1, Nat.eq_of_beq_eq_true rb1.2]
  · change rebuild (levels ()) h2β = _
    rw [rebuild_eq rb2.1, Nat.eq_of_beq_eq_true rb2.2]

theorem bindG : BindA 1782 11 pairGs E.ng E.G := by
  rw [hng]
  exact ⟨rfl, hG⟩

theorem hkeys : keys.toList = suzFiveKeys := by decide +kernel

theorem okE : CFSG.KC.BfsPin.bfsK 1782 11 E.ng E.G E.N E.T E.E E.S = true :=
  CFSG.KC.BfsPin.bfsK_of_slices (L := 27) (K := 15) (C := E.C) (hN.trans (by norm_num))
    (by norm_num) hw E.g E.csAll E.t0 E.dist (Nat.eq_of_beq_eq_true E.c0)
    (Nat.eq_of_beq_eq_true E.cK) E.rsAll

theorem enumP : enumOK 1782 pairGs suzFiveKeys (enumBfs 1782 pairGs suzFiveKeys 1000) = true ∧
    (enumBfs 1782 pairGs suzFiveKeys 1000).pts.size = E.N := by
  have h := enum_of (fuel := 1000) bindG (fun k hk => (gens k (by rw [hng] at hk; exact hk)).1)
    okE (by rw [hkeys]; decide) E.keys (by rw [hN]; omega)
  rw [hkeys] at h
  exact ⟨h.1, h.2.1⟩

theorem pair_ok : pairEqCheck () = true := by
  have hgk : ∀ k < 2, (okP (levels ()) pairGs[k]! && commA 1782 pairGs[k]! (rebuild (levels ()) xAβ) &&
      eqA 1782 (powArr 1782 pairGs[k]! 5) (idA 1782) && !(eqA 1782 pairGs[k]! (idA 1782))) = true := by
    intro k hk
    obtain ⟨hp, hc, h5, h1⟩ := gens k hk
    rw [hG k hk, hX]
    unfold okP inP commA CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
    rw [validA_of hp, siftA_of Suz2306.binds Suz2306.perm SuzC.hl (siftG k hk),
      comp_unpack' hw hp pX, comp_unpack' hw pX hp,
      eqA_unpack' hw (permB_pcomp hw hp pX) (permB_pcomp hw pX hp), powEq_id hw hp, eqA_id hw hp]
    change (true && true && Nat.beq (cm 1782 11 (E.G k) XA) (cm 1782 11 XA (E.G k)) &&
      Nat.beq (pw 1782 11 (E.G k) 5) (pidn 1782 11) && !Nat.beq (E.G k) (pidn 1782 11)) = true
    rw [hc, h5, h1]
    rfl
  obtain ⟨he1, he2⟩ := enumP
  unfold pairEqCheck pairEqCheckG
  change (pairGs.size == 2 && allLt 2 (fun i => okP (levels ()) pairGs[i]! &&
      commA 1782 pairGs[i]! (rebuild (levels ()) xAβ) &&
      eqA 1782 (powArr 1782 pairGs[i]! 5) (idA 1782) && !(eqA 1782 pairGs[i]! (idA 1782))) &&
    (enumOK 1782 pairGs suzFiveKeys (enumBfs 1782 pairGs suzFiveKeys 1000) &&
      (enumBfs 1782 pairGs suzFiveKeys 1000).pts.size == 405)) = true
  rw [he1, he2, hN, (allLt_iff).2 hgk]
  rfl

end CertificateChecks.KernelSuzPump

end
