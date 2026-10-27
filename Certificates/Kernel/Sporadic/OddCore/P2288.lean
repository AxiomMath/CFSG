module

public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.SmallOddCore.CountSplit
public import CFSG.Sporadic.SmallOddCore.McLCountA
public import CFSG.Sporadic.Schreier.PairMcLPairs
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Certificate2240
public import Certificates.Certificate2241
public import Certificates.Certificate2242
public import Certificates.Certificate2243
public import Certificates.Certificate2245
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.P2288

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def evPK (pat : List Bool) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun b _ ih p => strictN (ih p) (fun q =>
      pg 9 (mask 9) (nIf(b, CertificateChecks.KernelCensus.McLS.F 1,
        CertificateChecks.KernelCensus.McLS.F 0)) q)) pat p

@[expose] noncomputable def powPK (pat : List Bool) (e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ acc => strictN acc (fun q => evPK pat q)) e

@[expose] noncomputable def fixPK (pat : List Bool) (e : Nat) : Bool :=
  [0, 1, 2, 3, 4].all (fun b => powPK pat e b == b)

theorem k_ok : bAnd(canonK 275 9 (mask 9) (275 * 9) (CertificateChecks.KernelCensus.McLS.F 0),
    bAnd(canonK 275 9 (mask 9) (275 * 9) (CertificateChecks.KernelCensus.McLS.F 1),
    bAnd(fixPK [false, true, true] 12, bAnd(bIf(fixPK [false, true, true] 6, false, true),
    bAnd(bIf(fixPK [false, true, true] 4, false, true),
    bAnd(bIf(fixPK [false, true, true] 3, false, true),
    bAnd(bIf(fixPK [false, true, true] 2, false, true),
    bAnd(bIf(fixPK [false, true, true] 1, false, true),
    bAnd(fixPK mclWPat 7, bIf(fixPK mclWPat 1, false, true)))))))))) = true := by
  quickRfl

theorem canonF {j : Nat} (hj : j < 2) :
    canonK 275 9 (mask 9) (275 * 9) (CertificateChecks.KernelCensus.McLS.F j) = true := by
  have h := k_ok
  simp only [bAnd_iff] at h
  interval_cases j
  · exact h.1
  · exact h.2.1

theorem pg_lt {p x : Nat} (hp : canonK 275 9 (mask 9) (275 * 9) p = true) (hx : x < 275) :
    pg 9 (mask 9) p x < 275 := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  exact Eq.mp Nat.blt_eq (allN_spec hp.2.2 x hx)

theorem evR_cons (t : Array Nat) (w : List (Array Nat)) (p : Nat) :
    evR (t :: w) p = evR w t[p]! := rfl

theorem evR_append (u v : List (Array Nat)) (p : Nat) : evR (u ++ v) p = evR v (evR u p) := by
  unfold evR
  rw [List.foldl_append]

theorem evPK_cons (b : Bool) (pat : List Bool) (p : Nat) :
    evPK (b :: pat) p = pg 9 (mask 9) (nIf(b, CertificateChecks.KernelCensus.McLS.F 1,
      CertificateChecks.KernelCensus.McLS.F 0)) (evPK pat p) := by
  change strictN (evPK pat p) _ = _
  rw [sN]

theorem ev_eq : ∀ (pat : List Bool) (p : Nat), p < 275 →
    evR (patW PairMcL.wA PairMcL.wB pat) p = evPK pat p ∧ evPK pat p < 275
  | [], p, hp => ⟨rfl, hp⟩
  | b :: pat, p, hp => by
    obtain ⟨ih1, ih2⟩ := ev_eq pat p hp
    have hw : patW PairMcL.wA PairMcL.wB (b :: pat) =
        patW PairMcL.wA PairMcL.wB pat ++ (if b then PairMcL.wB else PairMcL.wA) := by
      unfold patW
      simp
    rw [hw, evR_append, ih1, evPK_cons]
    cases b
    · have h0 := canonF (j := 0) (by norm_num)
      refine ⟨?_, pg_lt h0 ih2⟩
      change evR [mclStrongArrs[0]!] (evPK pat p) = _
      rw [evR_cons, CertificateChecks.KernelCensus.McLK.mclStrongArrs_get 0 (by norm_num),
        CFSG.KC.Misc.PairCount.unpack_get ih2]
      rfl
    · have h1 := canonF (j := 1) (by norm_num)
      refine ⟨?_, pg_lt h1 ih2⟩
      change evR [mclStrongArrs[1]!] (evPK pat p) = _
      rw [evR_cons, CertificateChecks.KernelCensus.McLK.mclStrongArrs_get 1 (by norm_num),
        CFSG.KC.Misc.PairCount.unpack_get ih2]
      rfl

theorem pow_eq (pat : List Bool) : ∀ (e p : Nat), p < 275 →
    evPow (patW PairMcL.wA PairMcL.wB pat) e p = powPK pat e p ∧ powPK pat e p < 275
  | 0, p, hp => ⟨rfl, hp⟩
  | e + 1, p, hp => by
    obtain ⟨ih1, ih2⟩ := pow_eq pat e p hp
    have hs : powPK pat (e + 1) p = evPK pat (powPK pat e p) := by
      change strictN (powPK pat e p) (fun q => evPK pat q) = _
      rw [sN]
    rw [evPow, ih1, hs]
    exact ev_eq pat _ ih2

theorem fix_eq (pat : List Bool) (e : Nat) :
    fixB PairMcL.bs (patW PairMcL.wA PairMcL.wB pat) e = fixPK pat e := by
  unfold fixB fixPK
  have hb : PairMcL.bs = [0, 1, 2, 3, 4] := rfl
  rw [hb]
  simp only [List.all_cons, List.all_nil, (pow_eq pat e 0 (by norm_num)).1,
    (pow_eq pat e 1 (by norm_num)).1, (pow_eq pat e 2 (by norm_num)).1,
    (pow_eq pat e 3 (by norm_num)).1, (pow_eq pat e 4 (by norm_num)).1]

theorem nB {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem facts2288 : ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB [false, true, true]) 12 = true ∧
    ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB mclWPat) 7 = true := by
  have h := k_ok
  simp only [bAnd_iff] at h
  obtain ⟨-, -, h12, h6, h4, h3, h2, h1, h7, h71⟩ := h
  have d12 : CFSG.Sporadic.Schreier.Native.divParts 12 = [6, 4, 3, 2, 1] := by decide
  have d7 : CFSG.Sporadic.Schreier.Native.divParts 7 = [1] := by decide
  unfold ordB
  rw [d12, d7]
  have e6 := nB (b := fixPK [false, true, true] 6) h6
  have e4 := nB (b := fixPK [false, true, true] 4) h4
  have e3 := nB (b := fixPK [false, true, true] 3) h3
  have e2 := nB (b := fixPK [false, true, true] 2) h2
  have e1 := nB (b := fixPK [false, true, true] 1) h1
  have e71 := nB (b := fixPK mclWPat 1) h71
  simp only [fix_eq, List.all_cons, List.all_nil, h12, h7, e6, e4, e3, e2, e1, e71,
    Bool.not_false, Bool.and_self, and_self]

end CertificateChecks.KernelSpor.P2288

end
