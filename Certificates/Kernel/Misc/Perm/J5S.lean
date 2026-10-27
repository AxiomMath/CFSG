module

public import Certificates.Kernel.Misc.Perm.J5H
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

theorem bindsP : Binds 315 9 P.S 7 3 P.BP CFSG.Sporadic.Schreier.PairNative.j2StrongArrs
    CFSG.Sporadic.Schreier.PairJ2.baseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [
    CFSG.Sporadic.Schreier.PairNative.j2StrongArrs], fun j hj => ?_, by decide, by decide +kernel⟩
  have e : CFSG.Sporadic.Schreier.PairNative.j2StrongArrs[j]! =
      CFSG.Monster.B.Co2.Native.hexTable 4 315 (315 * j)
        CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
    simp [CFSG.Sporadic.Schreier.PairNative.j2StrongArrs, hj,
      CFSG.Sporadic.Schreier.PairNative.j2Strong]
  rw [e, JS.eq, CFSG.KC.Misc.HexFlat.hexTable_sound JS.all j hj]
  have hs : Nat.beq (JS.F j) (P.S j) = true := by interval_cases j <;> quickRfl
  rw [Nat.eq_of_beq_eq_true hs]

theorem permP : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (P.S j) (P.SI j)) = true := by
  quickRfl

@[expose] noncomputable def sP (G : ℕ) : Bool :=
  siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) P.LR P.TRI P.BP 3 0 G

theorem inP_of {G : ℕ} (hz : Nat.beq (Nat.shiftRight G (315 * 9)) 0 = true)
    (hr : allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315) = true) (hs : sP G = true) :
    j2FiveInP (unpack 315 9 G) = true :=
  siftK_soundR bindsP permP P.hl rfl (Nat.eq_of_beq_eq_true hz) hr hs

theorem inR_of {G : ℕ} (hG : permB 315 9 G = true)
    (h : (Nat.beq (Nat.shiftRight G (315 * 9)) 0 && sP G ||
      Nat.beq (Nat.shiftRight (cm (GR 2) G) (315 * 9)) 0 &&
        allN 315 (fun i => Nat.blt (pg 9 (mask 9) (cm (GR 2) G) i) 315) &&
        sP (cm (GR 2) G)) = true) :
    j2FiveInR (unpack 315 9 G) = true := by
  rw [j2FiveInR, Bool.or_eq_true]
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hz, hs⟩ | ⟨⟨hz, hr⟩, hs⟩
  · exact Or.inl (inP_of hz (range_of_permOK hG) hs)
  · right
    rw [hGR 2 (by norm_num), comp_unpack' hw (by quickRfl) hG]
    exact inP_of hz hr hs

end CertificateChecks.KernelMisc.J2F

end
