module

public import Certificates.Kernel.SchreierFam.C188001K
public import Certificates.Kernel.SchreierFam.C188001T
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.D4Sound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.U38B

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu

theorem permArr_eq {k : Nat} (hk : k < 32) : permArr k = unpack 513 10 (PF k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelSchreierFam.U38A.all k hk
  rw [← CertificateChecks.KernelSchreierFam.U38A.eq] at h
  exact h

theorem pPF {k : Nat} (hk : 25 ≤ k) (hk' : k < 32) : permB 513 10 (PF k) = true := by
  have h := allN_spec pP (k - 25) (by omega)
  have e : Nat.add 25 (k - 25) = k := by
    change 25 + (k - 25) = k
    omega
  rwa [e] at h

theorem strong1_get {j : Nat} (hj : j < 14) : strong1[j]! = permArr j := by
  interval_cases j <;> rfl

theorem strong2_get {j : Nat} (hj : j < 16) : strong2[j]! = permArr (idx2 j) := by
  interval_cases j <;> rfl

theorem binds1 : Binds 513 10 U38C1.S 14 3 U38C1.BP strong1 base1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, fun j hj => ?_, rfl, bget1⟩
  rw [strong1_get hj, permArr_eq (by omega), ← Nat.eq_of_beq_eq_true (allN_spec bS1 j hj)]

theorem binds2 : Binds 513 10 U38C2.S 16 5 U38C2.BP strong2 base2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, fun j hj => ?_, rfl, bget2⟩
  have hidx : idx2 j < 32 := by unfold idx2; split <;> omega
  rw [strong2_get hj, permArr_eq hidx, ← Nat.eq_of_beq_eq_true (allN_spec bS2 j hj)]

theorem words1_eq : words1 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 14 U38.d1 :=
  wordsArr_eq (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem words2_eq : words2 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 9 16 U38.d2 :=
  wordsArr_eq (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem chain1 : rawChainOK 513 (strong1.extract 0 9) strong1 base1 words1 1 = true := by
  rw [words1_eq]
  exact rawChainK_sound binds1 U38C1.head U38C1.hl hNS1 U38C1.hs

theorem chain2 : rawChainOK 513 (strong2.extract 0 9) strong2 base2 words2 1 = true := by
  rw [words2_eq]
  exact rawChainK_sound binds2 U38C2.head U38C2.hl hNS2 U38C2.hs

theorem orbs1 : rawOrbitSizes 513 strong1 base1 = [513, 512, 378] := by
  rw [rawOrbitSizesK_sound binds1 perm1 U38C1.hl]
  exact orb1

theorem sift1_of {G : Nat} (h : sift1 G = true) :
    siftA 513 (rawLevels 513 strong1 base1) base1 0 (unpack 513 10 G) = true := by
  unfold sift1 at h
  simp only [bAnd_iff] at h
  exact siftA_of binds1 perm1 U38C1.hl h

theorem sift2_of {G : Nat} (h : sift2 G = true) :
    siftA 513 (rawLevels 513 strong2 base2) base2 0 (unpack 513 10 G) = true := by
  unfold sift2 at h
  simp only [bAnd_iff] at h
  exact siftA_of binds2 perm2 U38C2.hl h

theorem s1 : sift1 (PF 25) = true ∧ sift1 (PF 30) = true ∧ sift1 (PF 31) = true ∧
    sift1 (U38E1.G 0) = true := by
  have h := sifts1
  simp only [bAnd_iff] at h
  exact h

theorem s2 : sift2 (PF 27) = true ∧ sift2 (U38E2.G 0) = true ∧ sift2 (U38E2.G 1) = true := by
  have h := sifts2
  simp only [bAnd_iff] at h
  exact h

theorem pw' : Nat.beq (pw 513 10 (PF 25) 19) I = true ∧ Nat.beq (pw 513 10 (PF 25) 1) I = false ∧
    Nat.beq (pw 513 10 (PF 27) 2) I = true ∧ Nat.beq (pw 513 10 (PF 27) 1) I = false ∧
    Nat.beq (pw 513 10 (PF 28) 9) I = true ∧ Nat.beq (pw 513 10 (PF 28) 3) I = false ∧
    Nat.beq (pw 513 10 (PF 30) 9) I = true ∧ Nat.beq (pw 513 10 (PF 30) 3) I = false ∧
    Nat.beq (pw 513 10 (PF 31) 7) I = true ∧ Nat.beq (pw 513 10 (PF 31) 1) I = false := by
  have h := pows
  simp only [bAnd_iff, Bool.not_eq_true'] at h
  exact h

theorem eqPow {k : Nat} (hk : 25 ≤ k) (hk' : k < 32) (e : Nat) :
    eqA 513 (powArr 513 (unpack 513 10 (PF k)) e) (idA 513) = Nat.beq (pw 513 10 (PF k) e) I :=
  powEq_id kW (pPF hk hk') e

theorem hN1 : U38E1.N = 57 ∧ U38E1.ng = 1 ∧ U38E1.G 0 = PF 26 := by
  have h := n1
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem hN2 : U38E2.N = 3024 ∧ U38E2.ng = 2 ∧ U38E2.G 0 = PF 28 ∧ U38E2.G 1 = PF 29 := by
  have h := n2
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem bindG1 : BindA 513 10 gens1 U38E1.ng U38E1.G := by
  refine ⟨by rw [hN1.2.1]; rfl, fun j hj => ?_⟩
  rw [hN1.2.1] at hj
  interval_cases j
  rw [hN1.2.2, ← permArr_eq (by norm_num)]
  rfl

theorem bindG2 : BindA 513 10 gens2 U38E2.ng U38E2.G := by
  refine ⟨by rw [hN2.2.1]; rfl, fun j hj => ?_⟩
  rw [hN2.2.1] at hj
  interval_cases j
  · rw [hN2.2.2.1, ← permArr_eq (by norm_num)]
    rfl
  · rw [hN2.2.2.2, ← permArr_eq (by norm_num)]
    rfl

theorem pG1 : ∀ k < U38E1.ng, permB 513 10 (U38E1.G k) = true := fun k hk => by
  have h := allN_spec comm1 k (by rw [hN1.2.1] at hk; exact hk)
  rw [Bool.and_eq_true] at h
  exact h.1

theorem pG2 : ∀ k < U38E2.ng, permB 513 10 (U38E2.G k) = true := fun k hk => by
  have h := allN_spec comm2 k (by rw [hN2.2.1] at hk; exact hk)
  rw [Bool.and_eq_true] at h
  exact h.1

theorem enum1 : enumOK 513 gens1 base1.toList (enumBfs 513 gens1 base1.toList 100) = true ∧
    (enumBfs 513 gens1 base1.toList 100).pts.size = U38E1.N ∧
    ∀ i < U38E1.N, (enumBfs 513 gens1 base1.toList 100).pts[i]! = unpack 513 10 (U38E1.T i) :=
  enum_of bindG1 pG1 U38E1.ok (mem_base_lt binds1 U38C1.hl) U38E1.keys (by rw [hN1.1]; omega)

theorem ok2 : CFSG.KC.BfsPin.bfsK 513 10 U38E2.ng U38E2.G U38E2.N U38E2.T U38E2.E U38E2.S = true :=
  CFSG.KC.BfsPin.bfsK_of_slices (L := 56) (K := 54) (C := U38E2.C) (by decide) (by norm_num) kW
    U38E2.g U38E2.csAll U38E2.t0 U38E2.dist (Nat.eq_of_beq_eq_true U38E2.c0)
    (Nat.eq_of_beq_eq_true U38E2.cK) U38E2.rsAll

theorem enum2 : enumOK 513 gens2 base2.toList (enumBfs 513 gens2 base2.toList 3100) = true ∧
    (enumBfs 513 gens2 base2.toList 3100).pts.size = U38E2.N ∧
    ∀ i < U38E2.N, (enumBfs 513 gens2 base2.toList 3100).pts[i]! = unpack 513 10 (U38E2.T i) :=
  enum_of bindG2 pG2 ok2 (mem_base_lt binds2 U38C2.hl) U38E2.keys (by rw [hN2.1]; omega)

theorem tail2 : allN 513 (ptailBranchK 513 10 U38C2.LR U38C2.TR U38C2.BP (PF 27)
    (pw 513 10 (PF 27)) rels2 U38E2.N U38E2.T 5) = true :=
  CFSG.KC.D4K.allN_of_slices (L := 27) (K := 19) (by norm_num) U38T2.all

theorem rcnt0 : rcnt (U38C1.LR 0) = 513 ∧ rcnt (U38C2.LR 0) = 513 := by
  have h := rc
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem cent1 : centOKP 19 513 strong1 base1 (unpack 513 10 (PF 25)) rels1 gens1 ps1 cert1 57 =
    true := by
  obtain ⟨he1, he2, he3⟩ := enum1
  have h := centOKP_of (p := 19) kW binds1 perm1 U38C1.hl (pPF (k := 25) (by norm_num)
    (by norm_num)) rels1K bindG1 comm1 (fun k hk => by
      rw [hN1.2.1] at hk
      interval_cases k
      exact sift1_of s1.2.2.2) he1 he2 he3 (allN_spec U38E1.perm) (by norm_num)
    (by rw [rcnt0.1]; exact tail1)
  rw [hN1.1] at h
  exact h

theorem cent2 : centOKP 2 513 strong2 base2 (unpack 513 10 (PF 27)) rels2 gens2 ps2 cert2 3024 =
    true := by
  obtain ⟨he1, he2, he3⟩ := enum2
  have h := centOKP_of (p := 2) kW binds2 perm2 U38C2.hl (pPF (k := 27) (by norm_num)
    (by norm_num)) rels2K bindG2 comm2 (fun k hk => by
      rw [hN2.2.1] at hk
      interval_cases k
      · exact sift2_of s2.2.1
      · exact sift2_of s2.2.2) he1 he2 he3 (CFSG.KC.D4K.permB_pts ok2 pG2) (by norm_num)
    (by rw [rcnt0.2]; exact tail2)
  rw [hN2.1] at h
  exact h

theorem x19_ok : validA 513 x19 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 x19 = true ∧
    eqA 513 (powArr 513 x19 19) (idA 513) = true ∧ eqA 513 (powArr 513 x19 1) (idA 513) = false ∧
    centOKP 19 513 strong1 base1 x19 rels1 gens1 ps1 cert1 57 = true := by
  have hx : x19 = unpack 513 10 (PF 25) := permArr_eq (by norm_num)
  rw [hx, eqPow (by norm_num) (by norm_num), eqPow (by norm_num) (by norm_num)]
  exact ⟨validA_of (pPF (by norm_num) (by norm_num)), sift1_of s1.1, pw'.1, pw'.2.1, cent1⟩

theorem sigma0_ok : validA 513 sigma0 = true ∧
    siftA 513 (rawLevels 513 strong2 base2) base2 0 sigma0 = true ∧
    eqA 513 (powArr 513 sigma0 2) (idA 513) = true ∧ eqA 513 (powArr 513 sigma0 1) (idA 513) = false ∧
    sigma0[base2[0]!]! = base2[0]! ∧ sigma0[base2[1]!]! = base2[1]! ∧ base2[0]! ≠ base2[1]! ∧
    centOKP 2 513 strong2 base2 sigma0 rels2 gens2 ps2 cert2 3024 = true ∧
    eqA 513 (powArr 513 gens2[0]! 9) (idA 513) = true ∧
    eqA 513 (powArr 513 gens2[0]! 3) (idA 513) = false := by
  have hs : sigma0 = unpack 513 10 (PF 27) := permArr_eq (by norm_num)
  have hg : gens2[0]! = unpack 513 10 (PF 28) := by
    rw [← permArr_eq (by norm_num)]
    rfl
  have b0 : base2[0]! = 84 := by decide
  have b1 : base2[1]! = 154 := by decide
  have hf := fixes
  simp only [bAnd_iff] at hf
  rw [hs, hg, b0, b1, eqPow (by norm_num) (by norm_num), eqPow (by norm_num) (by norm_num),
    eqPow (by norm_num) (by norm_num), eqPow (by norm_num) (by norm_num),
    CFSG.KC.Misc.PairCount.unpack_get (by norm_num), CFSG.KC.Misc.PairCount.unpack_get (by norm_num)]
  exact ⟨validA_of (pPF (by norm_num) (by norm_num)), sift2_of s2.1, pw'.2.2.1, pw'.2.2.2.1,
    Nat.eq_of_beq_eq_true hf.1, Nat.eq_of_beq_eq_true hf.2.1, by norm_num, cent2, pw'.2.2.2.2.1,
    pw'.2.2.2.2.2.1⟩

theorem y9_ok : validA 513 y9 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 y9 = true ∧
    eqA 513 (powArr 513 y9 9) (idA 513) = true ∧ eqA 513 (powArr 513 y9 3) (idA 513) = false ∧
    y9[base1[0]!]! = base1[0]! := by
  have hy : y9 = unpack 513 10 (PF 30) := permArr_eq (by norm_num)
  have b0 : base1[0]! = 0 := by decide
  have hf := fixes
  simp only [bAnd_iff] at hf
  rw [hy, b0, eqPow (by norm_num) (by norm_num), eqPow (by norm_num) (by norm_num),
    CFSG.KC.Misc.PairCount.unpack_get (by norm_num)]
  exact ⟨validA_of (pPF (by norm_num) (by norm_num)), sift1_of s1.2.1, pw'.2.2.2.2.2.2.1,
    pw'.2.2.2.2.2.2.2.1, Nat.eq_of_beq_eq_true hf.2.2⟩

theorem x7_ok : validA 513 x7 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 x7 = true ∧
    eqA 513 (powArr 513 x7 7) (idA 513) = true ∧ eqA 513 (powArr 513 x7 1) (idA 513) = false ∧
    ((List.range 513).filter fun p => x7[p]! == p).length = 2 := by
  have hx : x7 = unpack 513 10 (PF 31) := permArr_eq (by norm_num)
  rw [hx, eqPow (by norm_num) (by norm_num), eqPow (by norm_num) (by norm_num)]
  refine ⟨validA_of (pPF (by norm_num) (by norm_num)), sift1_of s1.2.2.1, pw'.2.2.2.2.2.2.2.2.1,
    pw'.2.2.2.2.2.2.2.2.2, ?_⟩
  rw [← fix7]
  exact congrArg List.length (List.filter_congr fun p hp => by
    rw [CFSG.KC.Misc.PairCount.unpack_get (List.mem_range.1 hp)])

open CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu in
open Certificates in
theorem facts :
    (rawChainOK 513 (strong1.extract 0 9) strong1 base1 words1 1 = true ∧
      rawOrbitSizes 513 strong1 base1 = [513, 512, 378]) ∧
    (rawChainOK 513 (strong2.extract 0 9) strong2 base2 words2 1 = true) ∧
    (validA 513 x19 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 x19 = true ∧
      eqA 513 (powArr 513 x19 19) (idA 513) = true ∧ eqA 513 (powArr 513 x19 1) (idA 513) = false ∧
      centOKP 19 513 strong1 base1 x19 rels1 gens1 ps1 cert1 57 = true) ∧
    (validA 513 sigma0 = true ∧ siftA 513 (rawLevels 513 strong2 base2) base2 0 sigma0 = true ∧
      eqA 513 (powArr 513 sigma0 2) (idA 513) = true ∧ eqA 513 (powArr 513 sigma0 1) (idA 513) = false ∧
      sigma0[base2[0]!]! = base2[0]! ∧ sigma0[base2[1]!]! = base2[1]! ∧ base2[0]! ≠ base2[1]! ∧
      centOKP 2 513 strong2 base2 sigma0 rels2 gens2 ps2 cert2 3024 = true ∧
      eqA 513 (powArr 513 gens2[0]! 9) (idA 513) = true ∧
      eqA 513 (powArr 513 gens2[0]! 3) (idA 513) = false) ∧
    (validA 513 y9 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 y9 = true ∧
      eqA 513 (powArr 513 y9 9) (idA 513) = true ∧ eqA 513 (powArr 513 y9 3) (idA 513) = false ∧
      y9[base1[0]!]! = base1[0]!) ∧
    (validA 513 x7 = true ∧ siftA 513 (rawLevels 513 strong1 base1) base1 0 x7 = true ∧
      eqA 513 (powArr 513 x7 7) (idA 513) = true ∧ eqA 513 (powArr 513 x7 1) (idA 513) = false ∧
      ((List.range 513).filter fun p => x7[p]! == p).length = 2) :=
  ⟨⟨chain1, orbs1⟩, chain2, x19_ok, sigma0_ok, y9_ok, x7_ok⟩

end CertificateChecks.KernelSchreierFam.U38B
