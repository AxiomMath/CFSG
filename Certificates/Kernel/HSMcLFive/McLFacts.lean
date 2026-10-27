module

public import Certificates.Kernel.HSMcLFive.McLChecks
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.FiveLocKSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSMcLFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.BfsPin
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.FiveLocK CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CertificateChecks.KernelCensus CFSG.Sporadic.Schreier
open CFSG.Monster.B.Co2 (allLt_iff)

theorem arrG {j : ℕ} (hj : j < 76) : mcl275FiveArr j = unpack 275 9 (G j) := by
  rw [mcl275FiveArr, MF.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound MF.all j hj

theorem pG {j : ℕ} (hj : j < 76) : permB 275 9 (G j) = true := Orb.allN_iff.1 permG j hj

theorem mbindLit {gs : Array (Array ℕ)} {m c : ℕ} {T : ℕ → ℕ} (hs : gs.size = m) (hc : c + m ≤ 76)
    (hgs : ∀ j < m, gs[j]! = mcl275FiveArr (c + j))
    (hG : allN m (fun j => Nat.beq (T j) (G (c + j))) = true) : BindA 275 9 gs m T :=
  ⟨hs, fun j hj => by rw [hgs j hj, arrG (by omega), Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hG j hj)]⟩

theorem mbindF {gs : Array (Array ℕ)} {m c : ℕ} (hs : gs.size = m) (hc : c + m ≤ 76)
    (hgs : ∀ j < m, gs[j]! = mcl275FiveArr (c + j)) : BindA 275 9 gs m (fun j => G (c + j)) :=
  mbindLit hs hc hgs (Orb.allN_iff.2 fun _ _ => Nat.beq_refl _)

theorem permGc {m c : ℕ} (hc : c + m ≤ 76) : ∀ j < m, permB 275 9 (G (c + j)) = true :=
  fun _ hj => pG (by omega)

theorem mbindL : BindA 275 9 mcl275FiveLines 31 (fun j => G (2 + j)) :=
  mbindF (by simp [mcl275FiveLines]) (by norm_num) fun j hj => by
    unfold mcl275FiveLines
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, Nat.add_comm]

theorem mbindH : BindA 275 9 mcl275FiveTransporters 31 (fun j => G (33 + j)) :=
  mbindF (by simp [mcl275FiveTransporters]) (by norm_num) fun j hj => by
    unfold mcl275FiveTransporters
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, Nat.add_comm]

theorem mline_eq {j : ℕ} (hj : j < 31) : mcl275FiveLines[j]! = unpack 275 9 (G (2 + j)) :=
  mbindL.2 j hj

theorem mbindQ : BindA 275 9 mcl275FiveQGens 2 (fun j => G (0 + j)) :=
  mbindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem mbindC0 : BindA 275 9 mcl275FiveC0Gens 3 (fun j => G (64 + j)) :=
  mbindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem mbindC1 : BindA 275 9 mcl275FiveC1Gens 4 (fun j => G (67 + j)) :=
  mbindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem mbindA0 : BindA 275 9 mcl275FiveA0Gens 2 (fun j => G (71 + j)) :=
  mbindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem mbindA1 : BindA 275 9 mcl275FiveA1Gens 3 (fun j => G (73 + j)) :=
  mbindF rfl (by norm_num) fun j hj => by interval_cases j <;> rfl

theorem mhpk : ∀ p ∈ mcl275FiveKeys, p < 275 := by decide

abbrev MEnumFacts (gs : Array (Array ℕ)) (c : ArrCert) (N : ℕ) (T : ℕ → ℕ) : Prop :=
  enumOK 275 gs mcl275FiveKeys c = true ∧ c.pts.size = N ∧ ∀ i < N, c.pts[i]! = unpack 275 9 (T i)

theorem menum {gs : Array (Array ℕ)} {m c N0 N fuel : ℕ} {GG T E S : ℕ → ℕ} {SK : List ℕ}
    (hb : BindA 275 9 gs m (fun j => G (c + j))) (hc : c + m ≤ 76) (hng : Nat.beq N0 m = true)
    (hG : allN m (fun j => Nat.beq (GG j) (G (c + j))) = true)
    (hk : CFSG.KC.BfsPin.bfsK 275 9 N0 GG N T E S = true)
    (hK : keysSK 275 9 mcl275FiveKeys N T SK = true) (hf : N ≤ fuel) :
    MEnumFacts gs (enumBfs 275 gs mcl275FiveKeys fuel) N T := by
  rw [Nat.eq_of_beq_eq_true hng] at hk
  exact enum_of (mbindLit hb.1 hc (fun j hj => by rw [hb.2 j hj, arrG (by omega)]) hG)
    (fun k hk' => by
      rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hG k hk')]
      exact pG (by omega)) hk mhpk hK hf

theorem mbinds0 : Binds 275 9 M0.S 14 8 M0.BP mcl275Case0Arrs mcl275Case0BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [mcl275Case0Arrs], fun j hj => ?_,
    by decide +kernel, mbget0⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound M0X.all j hj
  rw [← M0X.eq] at h
  rw [mcl275Case0Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, h,
    ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 mchains.1 j hj)]

theorem mbinds1 : Binds 275 9 M1.S 16 8 M1.BP mcl275Case1Arrs mcl275Case1BaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [mcl275Case1Arrs], fun j hj => ?_,
    by decide +kernel, mbget1⟩
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound M1X.all j hj
  rw [← M1X.eq] at h
  rw [mcl275Case1Arrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, h,
    ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 mchains.2 j hj)]

theorem mcaseChain_of {kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} {D : List (List ℤ)} (hb : Binds 275 9 PS kS nb BP S base)
    (hp : allN kS (fun j => permOK 275 9 (mask 9) (275 * 9) (PS j) (PSI j)) = true)
    (hh : headK 275 9 (mask 9) (275 * 9) (pidn 275 9) PS PSI kS 3 D nb BP = true)
    (hl : LevelsOK 275 9 PS PSI LR TR TRI kS nb BP)
    (hs : ∀ i < nb, ∀ s < 5, schK 275 9 (mask 9) (275 * 9) (pidn 275 9) PS PSI LR TR TRI kS BP nb i
      (stepsAt 275 9 PS kS BP i) (s * 55) 55 = true)
    (hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 kS D = W) (hk : 3 ≤ kS)
    (h : (Nat.beq (PS 0) (McLS.F 0) && Nat.beq (PS 1) (McLS.F 1) &&
      Nat.beq (PS 2) (KernelMisc.HSMcL.MC.F 0)) = true) :
    caseChainOK 275 S base W mclStrongArrs[0]! mclStrongArrs[1]!
      (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true := by
  have hc := rawChainK_sound (chunks := 1) hb hh hl (by norm_num) hs
  rw [hW] at hc
  have hP : ∀ j < kS, permB 275 9 (PS j) = true := fun j hj =>
    permB_of_pp (pp_of_permOK msz (Orb.allN_iff.1 hp j hj))
  simp only [Bool.and_eq_true] at h
  unfold caseChainOK
  rw [hc, hb.2.2.2.2.1 0 (by omega), hb.2.2.2.2.1 1 (by omega), hb.2.2.2.2.1 2 (by omega),
    McLK.mclStrongArrs_get 0 (by norm_num), McLK.mclStrongArrs_get 1 (by norm_num),
    KernelMisc.HSMcL.mclOuter_eq, ← Nat.eq_of_beq_eq_true h.1.1, ← Nat.eq_of_beq_eq_true h.1.2,
    ← Nat.eq_of_beq_eq_true h.2, eqA_unpack' msz (hP 0 (by omega)) (hP 0 (by omega)),
    eqA_unpack' msz (hP 1 (by omega)) (hP 1 (by omega)),
    eqA_unpack' msz (hP 2 (by omega)) (hP 2 (by omega)), Nat.beq_refl, Nat.beq_refl, Nat.beq_refl]
  rfl

theorem mchain0 : caseChainOK 275 mcl275Case0Arrs mcl275Case0BaseArr mcl275Case0Words
    mclStrongArrs[0]! mclStrongArrs[1]!
    (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true :=
  mcaseChain_of mbinds0 mperm0 M0.head M0.hl M0.hs (by decide +kernel) (by norm_num) mheads.1

theorem mchain1 : caseChainOK 275 mcl275Case1Arrs mcl275Case1BaseArr mcl275Case1Words
    mclStrongArrs[0]! mclStrongArrs[1]!
    (CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true :=
  mcaseChain_of mbinds1 mperm1 M1.head M1.hl M1.hs (by decide +kernel) (by norm_num) mheads.2

theorem msiftPF {T : ℕ} (h : siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP T = true) :
    siftA 275 mcl275PLevels CFSG.Sporadic.Schreier.PairMcL.baseArr 0 (unpack 275 9 T) = true :=
  siftA_of_siftOK McLK.binds McLK.hperm McLC.hl h

theorem msiftRF {T : ℕ} (h : siftOK 275 9 5 KernelMisc.HSMcL.C3.LR KernelMisc.HSMcL.C3.TRI
    KernelMisc.HSMcL.C3.BP T = true) :
    siftA 275 mcl275RLevels mcl275RBaseArr 0 (unpack 275 9 T) = true :=
  siftA_of_siftOK KernelMisc.HSMcL.c3_binds KernelMisc.HSMcL.c3_perm KernelMisc.HSMcL.C3.hl h

theorem menumQ : MEnumFacts mcl275FiveQGens mcl275FiveQCert 125 NQ.T := by
  have h := menum (fuel := 130) mbindQ (by norm_num) mnums.2.1 mgens.1 NQ.ok NQ.keys
    (by rw [Nat.eq_of_beq_eq_true mnums.1]; omega)
  rw [Nat.eq_of_beq_eq_true mnums.1] at h
  exact h

theorem menumC0 : MEnumFacts mcl275FiveC0Gens mcl275FiveC0Cert 50 NC0.T := by
  have h := menum (fuel := 60) mbindC0 (by norm_num) mnums.2.2.2.1 mgens.2.1 NC0.ok NC0.keys
    (by rw [Nat.eq_of_beq_eq_true mnums.2.2.1]; omega)
  rw [Nat.eq_of_beq_eq_true mnums.2.2.1] at h
  exact h

theorem menumC1 : MEnumFacts mcl275FiveC1Gens mcl275FiveC1Cert 1500 NC1.T := by
  have h := menum (fuel := 1600) mbindC1 (by norm_num) mnums.2.2.2.2.2.1 mgens.2.2.1 NC1.ok NC1.keys
    (by rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.1]; omega)
  rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.1] at h
  exact h

theorem menumA0 : MEnumFacts mcl275FiveA0Gens mcl275FiveA0Cert 25 NA0.T := by
  have h := menum (fuel := 30) mbindA0 (by norm_num) mnums.2.2.2.2.2.2.2.1 mgens.2.2.2.1 NA0.ok
    NA0.keys (by rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.2.2.1]; omega)
  rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.2.2.1] at h
  exact h

theorem menumA1 : MEnumFacts mcl275FiveA1Gens mcl275FiveA1Cert 125 NA1.T := by
  have h := menum (fuel := 130) mbindA1 (by norm_num) mnums.2.2.2.2.2.2.2.2.2 mgens.2.2.2.2 NA1.ok
    NA1.keys (by rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.2.2.2.2.1]; omega)
  rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.2.2.2.2.1] at h
  exact h

theorem mpQ : ∀ i < 125, permB 275 9 (NQ.T i) = true := fun i hi =>
  Orb.allN_iff.1 NQ.perm i (by rw [Nat.eq_of_beq_eq_true mnums.1]; exact hi)

theorem mpC0 : ∀ i < 50, permB 275 9 (NC0.T i) = true := fun i hi =>
  Orb.allN_iff.1 NC0.perm i (by rw [Nat.eq_of_beq_eq_true mnums.2.2.1]; exact hi)

theorem mpC1 : ∀ i < 1500, permB 275 9 (NC1.T i) = true := fun i hi =>
  Orb.allN_iff.1 NC1.perm i (by rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.1]; exact hi)

theorem mpA0 : ∀ i < 25, permB 275 9 (NA0.T i) = true := fun i hi =>
  Orb.allN_iff.1 NA0.perm i (by rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.2.2.1]; exact hi)

theorem mpA1 : ∀ i < 125, permB 275 9 (NA1.T i) = true := fun i hi =>
  Orb.allN_iff.1 NA1.perm i (by rw [Nat.eq_of_beq_eq_true mnums.2.2.2.2.2.2.2.2.1]; exact hi)

theorem mqfacts : linesOK 275 mcl275FiveQGens mcl275FiveKeys mcl275FiveQCert mcl275FiveLines = true ∧
    allLt mcl275FiveQGens.size (fun l => siftA 275 mcl275PLevels
      CFSG.Sporadic.Schreier.PairMcL.baseArr 0 mcl275FiveQGens[l]!) = true ∧
    transOK 275 mcl275FiveTransporters mcl275FiveLines mcl275FiveRec mcl275RLevels
      mcl275RBaseArr = true ∧
    mcl275FiveRec.getD 0 0 = 0 ∧ mcl275FiveRec.getD 1 0 = 1 ∧
    allLt 31 (fun j => mcl275FiveRec.getD j 0 == 0 || mcl275FiveRec.getD j 0 == 1) = true := by
  obtain ⟨h1, h2, h3⟩ := menumQ
  refine ⟨linesOK_of msz h1 h2 h3 mpQ mbindL mlines, ?_,
    transOK_of msz mbindH mbindL (permGc (by norm_num)) (fun j hj => by
      rw [mbindH.2 j hj]
      exact msiftRF (Orb.allN_iff.1 msiftH j hj)) mtrans, by decide, by decide,
    by rw [allLt_iff]; decide⟩
  rw [allLt_iff]
  intro l hl
  have hl2 : l < 2 := hl
  rw [mbindQ.2 l hl2]
  exact msiftPF (by simpa only [Nat.zero_add] using Orb.allN_iff.1 msiftQ l hl2)

theorem mcase0 : caseChainOK 275 mcl275Case0Arrs mcl275Case0BaseArr mcl275Case0Words
      mclStrongArrs[0]! mclStrongArrs[1]! (CFSG.Sporadic.SmallOddCore.Native.natArr
        CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
    centOK 275 mcl275Case0Arrs mcl275Case0BaseArr mcl275FiveLines[0]! mcl275Case0Rels
      mcl275FiveC0Gens mcl275FiveKeys mcl275FiveC0Cert 50 = true ∧
    normalOK 275 mcl275FiveC0Gens mcl275FiveA0Gens mcl275FiveKeys mcl275FiveC0Cert
      mcl275FiveA0Cert 25 mcl275PLevels CFSG.Sporadic.Schreier.PairMcL.baseArr = true ∧
    selfCentOK 275 mcl275FiveA0Gens mcl275FiveC0Cert mcl275FiveA0Cert = true ∧
    eqA 275 mcl275FiveC0Gens[0]! mcl275FiveLines[0]! = true := by
  obtain ⟨c1, c2, c3⟩ := menumC0
  obtain ⟨a1, a2, a3⟩ := menumA0
  refine ⟨mchain0, ?_, ?_, ?_, ?_⟩
  · rw [centOK_eq, mline_eq (by norm_num)]
    have htail : allN (rcnt (M0.LR 0)) (ptailBranchK 275 9 M0.LR M0.TR M0.BP (G 2)
        (pw 275 9 (G 2)) mcl275Case0Rels 50 NC0.T 8) = true := by
      rw [Nat.eq_of_beq_eq_true mrc.1, ← Nat.eq_of_beq_eq_true mnums.2.2.1]
      exact ptailBranchIdxK_le (ES := NC0.S) (allN_of_blocks (L := 25) (K := 11)
        (f := ptailBranchIdxK 275 9 M0.LR M0.TR M0.BP (G 2) (pw 275 9 (G 2)) mcl275Case0Rels NC0.N
          NC0.T NC0.S 8) tailU_all)
    exact centOKP_of msz mbinds0 mperm0 M0.hl (pG (by norm_num)) mrels0 mbindC0 mcomm0
      (fun k hk => siftA_of_siftOK mbinds0 mperm0 M0.hl (Orb.allN_iff.1 msiftC0 k hk)) c1 c2 c3
      mpC0 (by norm_num) htail
  · rw [normalOK_eq]
    exact normalOKP_of msz a1 a2 a3 mpA0 c2 c3 mpC0 mbindC0 (permGc (by norm_num)) mbindA0
      (permGc (by norm_num)) (fun l hl => msiftPF (Orb.allN_iff.1 msiftA0 l hl)) rfl mnormal0
  · exact selfCentOK_of msz a2 a3 mpA0 c2 c3 mpC0 mbindA0 (permGc (by norm_num)) mself0
  · rw [mbindC0.2 0 (by norm_num), mline_eq (by norm_num), eqA_unpack' msz (pG (by norm_num))
      (pG (by norm_num))]
    exact meq0

theorem mcase1 : caseChainOK 275 mcl275Case1Arrs mcl275Case1BaseArr mcl275Case1Words
      mclStrongArrs[0]! mclStrongArrs[1]! (CFSG.Sporadic.SmallOddCore.Native.natArr
        CFSG.Sporadic.SmallOddCore.mclOuterTbl) = true ∧
    centOK 275 mcl275Case1Arrs mcl275Case1BaseArr mcl275FiveLines[1]! mcl275Case1Rels
      mcl275FiveC1Gens mcl275FiveKeys mcl275FiveC1Cert 1500 = true ∧
    normalOK 275 mcl275FiveC1Gens mcl275FiveA1Gens mcl275FiveKeys mcl275FiveC1Cert
      mcl275FiveA1Cert 125 mcl275PLevels CFSG.Sporadic.Schreier.PairMcL.baseArr = true ∧
    zCentOK 275 mcl275FiveA1Gens mcl275FiveC1Cert mcl275FiveA1Cert mcl275FiveLines[1]! = true ∧
    eqA 275 mcl275FiveC1Gens[0]! mcl275FiveLines[1]! = true := by
  obtain ⟨c1, c2, c3⟩ := menumC1
  obtain ⟨a1, a2, a3⟩ := menumA1
  refine ⟨mchain1, ?_, ?_, ?_, ?_⟩
  · rw [centOK_eq, mline_eq (by norm_num)]
    have htail : allN (rcnt (M1.LR 0)) (ptailBranchK 275 9 M1.LR M1.TR M1.BP (G 3)
        (pw 275 9 (G 3)) mcl275Case1Rels 1500 NC1.T 8) = true := by
      rw [Nat.eq_of_beq_eq_true mrc.2, ← Nat.eq_of_beq_eq_true mnums.2.2.2.2.1]
      exact ptailBranchIdxK_le (ES := NC1.S) (allN_of_blocks (L := 25) (K := 11)
        (f := ptailBranchIdxK 275 9 M1.LR M1.TR M1.BP (G 3) (pw 275 9 (G 3)) mcl275Case1Rels NC1.N
          NC1.T NC1.S 8) tailV_all)
    exact centOKP_of msz mbinds1 mperm1 M1.hl (pG (by norm_num)) mrels1 mbindC1 mcomm1
      (fun k hk => siftA_of_siftOK mbinds1 mperm1 M1.hl (Orb.allN_iff.1 msiftC1 k hk)) c1 c2 c3
      mpC1 (by norm_num) htail
  · rw [normalOK_eq]
    exact normalOKP_of msz a1 a2 a3 mpA1 c2 c3 mpC1 mbindC1 (permGc (by norm_num)) mbindA1
      (permGc (by norm_num)) (fun l hl => msiftPF (Orb.allN_iff.1 msiftA1 l hl)) rfl mnormal1
  · rw [mline_eq (by norm_num)]
    exact zCentOK_of msz a2 a3 mpA1 c2 c3 mpC1 mbindA1 (permGc (by norm_num)) (pG (by norm_num))
      mz1.1 mz1.2
  · rw [mbindC1.2 0 (by norm_num), mline_eq (by norm_num), eqA_unpack' msz (pG (by norm_num))
      (pG (by norm_num))]
    exact meq1

end CertificateChecks.KernelHSMcLFive

end
