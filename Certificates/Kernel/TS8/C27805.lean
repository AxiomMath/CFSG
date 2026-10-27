module

public import Certificates.Kernel.TS8.Checks
public import CFSG.Certificates.Kernel.TS8.EA16Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTS8

open CFSG.KC.TS8 CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
  CFSG.EvenSporadicStandard.Fin76b.TS8D8 CFSG.EvenSporadicStandard.Fin76b.TS8EA16
  CFSG.KS.SporSch.M24

theorem beqT {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ea16_of {n w ng : ℕ} {PA PB PU : ℕ} {ws : List (List ℕ)} {GW EP W Pa La S IT : ℕ → ℕ}
    {MT : ℕ → ℕ → ℕ} (hsz : szOK n w = true)
    (hperm : bAnd(permOK n w (mask w) (n * w) PA (pinvS n w (mask w) PA),
      bAnd(permOK n w (mask w) (n * w) PB (pinvS n w (mask w) PB),
        permOK n w (mask w) (n * w) PU (pinvS n w (mask w) PU))) = true)
    (hword : (allN ng fun k => Nat.beq (wordP n w PA PB PU (ws.getD k [])) (GW k)) = true)
    (hlen : Nat.beq ws.length ng = true) (hdist : sortDK EP S 256 = true)
    (hroot : bAnd(Nat.beq (EP 0) (pidn n w), bAnd(Nat.beq (Pa 0) 0, Nat.beq (La 0) 0)) = true)
    (htree : (allN 255 fun c => bAnd(Nat.blt (Pa (c + 1)) (c + 1),
      bAnd(Nat.blt (La (c + 1)) ng, Nat.beq (W (ng * Pa (c + 1) + La (c + 1))) (c + 1)))) = true)
    (hact : ∀ h < 256, ∀ k < ng, W (ng * h + k) < 256 ∧
      pcomp n w (mask w) (EP h) (GW k) = EP (W (ng * h + k)))
    (hrun : Nat.beq (orbRunK W Pa La ng 257 0 1) 256 = true) (hmt : mtK MT W Pa La ng = true)
    (hit : ∀ a < 256, IT a < 256 ∧ pinvS n w (mask w) (EP a) = EP (IT a))
    (hsearch : searchF (mF MT) (iF IT) = true)
    (hchain : bIf(hasChainF (mF MT) 5 [0] (invsF (mF MT)), false, true) = true) :
    checkEA16 n (unpack n w PA) (unpack n w PB) (unpack n w PU) ws = true := by
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at hperm hroot
  simp only [MatL.allN_iff, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at htree
  rw [MatL.allN_iff] at hword
  refine checkEA16_of_K (MT := MT) (IT := IT) hsz (PP_of_permOK hsz hperm.1)
    (PP_of_permOK hsz hperm.2.1) (PP_of_permOK hsz hperm.2.2) (beqT hlen)
    (fun k hk => beqT (hword k hk)) (sortDK_inj hdist) (beqT hroot.1) (beqT hroot.2.1)
    (beqT hroot.2.2) (fun c h0 hc => ?_) hact (beqT hrun) hmt hit hsearch ?_
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨h1, h2, h3⟩ := htree c' (by omega)
    exact ⟨h1, h2, beqT h3⟩
  · cases e : hasChainF (mF MT) 5 [0] (invsF (mF MT))
    · rfl
    · rw [e] at hchain
      exact absurd hchain (by decide)

theorem hA2 : CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[0]! = unpack 315 9 PA2 := by
  have e : CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[0]! = CFSG.Monster.B.Co2.Native.hexTable
      4 315 (315 * 0) CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
    simp [CFSG.Sporadic.Schreier.PairNative.j2StrongArrs, CFSG.Sporadic.Schreier.PairNative.j2Strong]
  rw [e, CertificateChecks.KernelMisc.J2F.JS.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelMisc.J2F.JS.all 0 (by norm_num)

theorem hB2 : CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[1]! = unpack 315 9 PB2 := by
  have e : CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[1]! = CFSG.Monster.B.Co2.Native.hexTable
      4 315 (315 * 1) CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
    simp [CFSG.Sporadic.Schreier.PairNative.j2StrongArrs, CFSG.Sporadic.Schreier.PairNative.j2Strong]
  rw [e, CertificateChecks.KernelMisc.J2F.JS.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelMisc.J2F.JS.all 1 (by norm_num)

theorem hU2 : CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j2CentTbl 0) =
    unpack 315 9 PU2 := by
  have e : CFSG.Sporadic.SmallOddCore.j2CentTbl 0 = CFSG.Sporadic.SmallOddCore.Native.hexT 3 315
      (315 * 0) CFSG.Sporadic.SmallOddCore.j2CentHex := rfl
  rw [e, CertificateChecks.KernelMisc.J2F.JU.eq]
  exact CFSG.KC.Misc.HexFlat.hexT_sound CertificateChecks.KernelMisc.J2F.JU.all (by norm_num) 0
    (by norm_num)

theorem act2' : ∀ h < 256, ∀ k < 3, W2 (3 * h + k) < 256 ∧
    pcomp 315 9 (mask 9) (EP2 h) (GW2 k) = EP2 (W2 (3 * h + k)) := by
  intro h hh k hk
  have e := MatL.allN_iff.1 (MatL.allN_iff.1 act2 h hh) k hk
  rw [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨e.1, beqT e.2⟩

theorem it2' : ∀ a < 256, IT2 a < 256 ∧ pinvS 315 9 (mask 9) (EP2 a) = EP2 (IT2 a) := by
  intro a ha
  have e := MatL.allN_iff.1 it2 a ha
  rw [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨e.1, beqT e.2⟩

theorem ea2 : checkEA16 315 (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[0]!)
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[1]!)
    (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j2CentTbl 0))
    j2SylowWords = true := by
  rw [hA2, hB2, hU2]
  exact ea16_of sz2 perm2 word2 len2 dist2 root2 tree2 act2' run2 mt2 it2' search2 chain2

theorem hS3 {k : ℕ} (hk : k < 5) :
    CFSG.Sporadic.Schreier.j3StrongArrs[k]! = unpack 6156 13 (CertificateChecks.KernelCensus.J3S.F k) := by
  have e : CFSG.Sporadic.Schreier.j3StrongArrs[k]! = CFSG.Monster.B.Co2.Native.hexTable 4 6156
      (6156 * k) CFSG.Sporadic.Schreier.j3StrongHex := by
    rw [CFSG.Sporadic.Schreier.j3StrongArrs, getElem!_pos _ k (by simpa using hk),
      Array.getElem_ofFn]
  rw [e, CertificateChecks.KernelCensus.J3S.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelCensus.J3S.all k hk

theorem hU3 : CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j3CentTbl 0) =
    unpack 6156 13 PU3 := by
  have e : CFSG.Sporadic.SmallOddCore.j3CentTbl 0 = CFSG.Sporadic.SmallOddCore.Native.hexT 4 6156
      (6156 * 0) CFSG.Sporadic.SmallOddCore.j3CentHex := rfl
  rw [e, CertificateChecks.KernelCensus.J3UT.eq]
  exact CFSG.KC.Misc.HexFlat.hexT_sound CertificateChecks.KernelCensus.J3UT.all (by norm_num) 0
    (by norm_num)

theorem act3' : ∀ h < 256, ∀ k < 4, W3 (4 * h + k) < 256 ∧
    pcomp 6156 13 (mask 13) (EP3 h) (GW3 k) = EP3 (W3 (4 * h + k)) := by
  intro h hh k hk
  have hb : act3 (h / 64) = true := by
    have hb : h / 64 < 4 := by omega
    generalize h / 64 = b at hb
    interval_cases b
    exacts [act3_0, act3_1, act3_2, act3_3]
  have e := MatL.allN_iff.1 (MatL.allN_iff.1 hb (h % 64) (Nat.mod_lt _ (by norm_num))) k hk
  rw [Nat.div_add_mod, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨e.1, beqT e.2⟩

theorem it3' : ∀ a < 256, IT3 a < 256 ∧ pinvS 6156 13 (mask 13) (EP3 a) = EP3 (IT3 a) := by
  intro a ha
  have hb : it3 (a / 64) = true := by
    have hb : a / 64 < 4 := by omega
    generalize a / 64 = b at hb
    interval_cases b
    exacts [it3_0, it3_1, it3_2, it3_3]
  have e := MatL.allN_iff.1 hb (a % 64) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨e.1, beqT e.2⟩

theorem ea3 : checkEA16 6156 (CFSG.Sporadic.Schreier.j3StrongArrs[0]!)
    (CFSG.Sporadic.Schreier.j3StrongArrs[1]!)
    (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j3CentTbl 0))
    j3SylowWords = true := by
  have hA3 : CFSG.Sporadic.Schreier.j3StrongArrs[0]! = unpack 6156 13 PA3 := by
    unfold PA3
    exact hS3 (by norm_num)
  have hB3 : CFSG.Sporadic.Schreier.j3StrongArrs[1]! = unpack 6156 13 PB3 := by
    unfold PB3
    exact hS3 (by norm_num)
  rw [hA3, hB3, hU3]
  exact ea16_of sz3 perm3 word3 len3 dist3 root3 tree3 act3' run3 mt3 it3' search3 chain3

open Certificates in
theorem c27805 : CFSG.EvenSporadicStandard.Fin76b.TS8EA16.checkEA16 315
      (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[0]!)
      (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[1]!)
      (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j2CentTbl 0))
      CFSG.EvenSporadicStandard.Fin76b.TS8D8.j2SylowWords = true ∧
    CFSG.EvenSporadicStandard.Fin76b.TS8EA16.checkEA16 6156
      (CFSG.Sporadic.Schreier.j3StrongArrs[0]!)
      (CFSG.Sporadic.Schreier.j3StrongArrs[1]!)
      (CFSG.Sporadic.SmallOddCore.Native.natArr (CFSG.Sporadic.SmallOddCore.j3CentTbl 0))
      CFSG.EvenSporadicStandard.Fin76b.TS8D8.j3SylowWords = true := ⟨ea2, ea3⟩

end CertificateChecks.KernelTS8

end
