module

public import Certificates.Kernel.LocalComp.McLYW
public import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.McLY

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.LocalComp.ConjPin CFSG.KC.LocalComp.Pin

theorem kBindG : (Nat.beq yG.size YE.ng && allN YE.ng fun k => bindArrK yG[k]! 11 4 (YE.G k)) =
    true := by quickRfl

theorem kBindGI : (Nat.beq yGI.size YE.ng && allN YE.ng fun k => bindArrK yGI[k]! 11 4 (YGI k)) =
    true := by quickRfl

theorem kOrb : ∀ l < 10, bfsCK 11 4 YE.ng YE.G YGI (YX l) (ySz l) (fun p => YA (yOff l + p))
    (fun p => YAE (yOff l + p)) (fun p => YAS (yOff l + p)) = true := by
  decide +kernel

theorem kX : ∀ l < 10, wordTabS 11 yG (mclYWords.getD l []) = unpack 11 4 (YX l) := by
  decide +kernel

theorem kNot : ∀ l < 10, ∀ l' < 10, l ≠ l' →
    notInK 11 4 (ySz l) (fun p => YA (yOff l + p)) (YX l') = true := by
  decide +kernel

theorem kCov : allN YE.N (fun i => bAnd(Nat.blt (Nat.land (YC i) (nat_lit 65535)) 10,
    bAnd(Nat.blt (Nat.shiftRight (YC i) (nat_lit 16)) (ySz (Nat.land (YC i) (nat_lit 65535))),
      Nat.beq (YA (yOff (Nat.land (YC i) (nat_lit 65535)) + Nat.shiftRight (YC i) (nat_lit 16)))
        (YE.T i)))) = true := by
  quickRfl

theorem kSz : ∀ l < 10, ySz l = mclYSizes.getD l 0 ∧ ySz l ≤ 2000 := by decide +kernel

theorem enumFacts : enumOK 11 mclYGens mclYEnum = true ∧
    mclYEnum.tabs = Array.ofFn (n := YE.N) fun i => unpack 11 4 (YE.T i.val) := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindG
  rw [mclYEnum, mclYGens_eq]
  exact enumBFS_of_bfsK (T := YE.T) (E := YE.E) (S := YE.S) hs hg YE.ok (by decide)

theorem enum : enumOK 11 mclYGens mclYEnum = true ∧ mclYEnum.tabs.size = 7920 := by
  refine ⟨enumFacts.1, ?_⟩
  rw [enumFacts.2, Array.size_ofFn]
  rfl

theorem orb_get (l : ℕ) (hl : l < 10) : mclYOrbits[l]! =
    orbitBFS 11 mclYGens mclYInvs (wordTabS 11 mclYGens (mclYWords.getD l [])) 2000 := by
  rw [mclYOrbits, getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]

theorem orbFacts (l : ℕ) (hl : l < 10) :
    treeOK (conjStep 11 mclYGens mclYInvs) mclYGens.size
      (wordTabS 11 mclYGens (mclYWords.getD l [])) mclYOrbits[l]! = true ∧
    mclYOrbits[l]!.tabs = Array.ofFn (n := ySz l) fun p => unpack 11 4 (YA (yOff l + p.val)) := by
  obtain ⟨hs, hg⟩ := binds_of_check kBindG
  obtain ⟨hsi, hgi⟩ := binds_of_check kBindGI
  rw [orb_get l hl, mclYInvs_eq, mclYGens_eq]
  exact orbitBFS_of_bfsCK (T := fun p => YA (yOff l + p)) (E := fun p => YAE (yOff l + p))
    (S := fun p => YAS (yOff l + p)) hs hsi hg hgi (kX l hl) (kOrb l hl) (kSz l hl).2

theorem orbits : (∀ l < 10, orbitOK 11 mclYGens mclYInvs (wordTabS 11 mclYGens
      (mclYWords.getD l [])) mclYOrbits[l]! = true ∧ mclYOrbits[l]!.tabs.size = mclYSizes.getD l 0) ∧
    (∀ l < 10, ∀ l' < 10, l ≠ l' →
      notInOK mclYOrbits[l]!.tabs (wordTabS 11 mclYGens (mclYWords.getD l' [])) = true) ∧
    (∀ l < 10, ∀ j ∈ mclYWords.getD l [], j < mclYGens.size) ∧
    wordTabS 11 mclYGens (mclYWords.getD 0 []) = idTab 11 := by
  have hinv : invsOK 11 mclYGens mclYInvs = true := basic.2.2.1
  refine ⟨fun l hl => ⟨?_, ?_⟩, fun l hl l' hl' hne => ?_, ?_, ?_⟩
  · rw [orbitOK, hinv, (orbFacts l hl).1]
    rfl
  · rw [(orbFacts l hl).2, Array.size_ofFn]
    exact (kSz l hl).1
  · rw [(orbFacts l hl).2, mclYGens_eq]
    exact notInOK_of_K (T := fun p => YA (yOff l + p)) (kX l' hl') (kNot l hl l' hl' hne)
  · rw [mclYGens_eq]
    decide +kernel
  · rw [mclYGens_eq]
    decide +kernel

theorem cover : coverAllOK mclYEnum.tabs mclYOrbits = true := by
  rw [enumFacts.2]
  exact coverAllOK_of_K (T := YE.T) (C := YC) (L := 10) (NL := ySz)
    (OT := fun l p => YA (yOff l + p))
    (by rw [mclYOrbits, Array.size_ofFn]) (fun l hl => (orbFacts l hl).2) kCov

end CertificateChecks.KernelLC.McLY
