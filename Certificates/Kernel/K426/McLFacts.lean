module

public import Certificates.Kernel.K426.McLChecks
public import Certificates.Kernel.K426.McLOrb
public import CFSG.Certificates.Kernel.Misc.ChainTailOrbSound
public import CFSG.Certificates.Kernel.K426KSound
public import Certificates.Kernel.Census.McLN
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelK426

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.RankThree.PartTwo.KFacts.K426 CertificateChecks.KernelCensus
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.Monster.B.Fischer
open CFSG.Monster.B.Co2 (allLt_iff)

theorem arr {k : ℕ} (hk : k < 339) : mcl3Arr k = unpack 275 9 (F k) := by
  rw [mcl3Arr, McLKT.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound McLKT.all k hk

theorem pF {k : ℕ} (hk : k < 339) : permB 275 9 (F k) = true := Orb.allN_iff.1 permF k hk

theorem getOfFn {m c j : ℕ} (hj : j < m) (hc : c + m ≤ 339) :
    (Array.ofFn fun i : Fin m => mcl3Arr (c + i.val))[j]! = unpack 275 9 (F (c + j)) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact arr (by omega)

theorem bindOfFn {m c : ℕ} (hc : c + m ≤ 339) :
    BindA 275 9 (Array.ofFn fun i : Fin m => mcl3Arr (c + i.val)) m (fun j => F (c + j)) :=
  ⟨by simp, fun _ hj => getOfFn hj hc⟩

theorem bindQ : BindA 275 9 mcl3QGens 4 (fun j => F (0 + j)) := bindOfFn (by norm_num)

theorem bindL : BindA 275 9 mcl3Lines 148 (fun j => F (4 + j)) := bindOfFn (by norm_num)

theorem bindH : BindA 275 9 mcl3Trans 148 (fun j => F (152 + j)) := bindOfFn (by norm_num)

theorem bindCA : BindA 275 9 mcl3CAGens 3 (fun j => F (316 + j)) := bindOfFn (by norm_num)

theorem bindO : BindA 275 9 mcl3OGens 5 (fun j => F (319 + j)) := bindOfFn (by norm_num)

theorem bindCB : BindA 275 9 mcl3CBGens 3 (fun j => F (336 + j)) := bindOfFn (by norm_num)

theorem bindE {gs : Array (Array ℕ)} {m c ng : ℕ} {G : ℕ → ℕ} (hb : BindA 275 9 gs m (fun j => F (c + j)))
    (hng : Nat.beq ng m = true) (hG : allN m (fun j => Nat.beq (G j) (F (c + j))) = true) :
    BindA 275 9 gs ng G := by
  rw [Nat.eq_of_beq_eq_true hng]
  refine ⟨hb.1, fun j hj => ?_⟩
  rw [hb.2 j hj, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hG j hj)]

theorem bindsA : Binds 275 9 MA.S 16 10 MA.BP mcl3ChainAArrs mcl3ChainABaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, (bindOfFn (c := 300) (m := 16) (by norm_num)).1,
    fun j hj => ?_, by decide +kernel, bgetA⟩
  refine ((bindOfFn (c := 300) (m := 16) (by norm_num)).2 j hj).trans ?_
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 chains.1 j hj)]

theorem bindsB : Binds 275 9 MB.S 12 10 MB.BP mcl3ChainBArrs mcl3ChainBBaseArr := by
  refine ⟨by norm_num, by norm_num, by norm_num, (bindOfFn (c := 324) (m := 12) (by norm_num)).1,
    fun j hj => ?_, by decide +kernel, bgetB⟩
  refine ((bindOfFn (c := 324) (m := 12) (by norm_num)).2 j hj).trans ?_
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 chains.2 j hj)]

theorem hps : ∀ p ∈ mcl3Keys, p < 275 := by decide

theorem siftP {G : ℕ} (h : siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP G = true) :
    siftA 275 PairMcL.levels PairMcL.baseArr 0 (unpack 275 9 G) = true :=
  siftA_of_siftOK McLK.binds McLK.hperm McLC.hl h

theorem permsOf {N : ℕ} {T : ℕ → ℕ} (h : allN N (fun i => permB 275 9 (T i)) = true) :
    ∀ i < N, permB 275 9 (T i) = true := Orb.allN_iff.1 h

abbrev EnumFacts (gs : Array (Array ℕ)) (c : ArrCert) (N : ℕ) (T : ℕ → ℕ) : Prop :=
  enumOK 275 gs mcl3Keys c = true ∧ c.pts.size = N ∧ ∀ i < N, c.pts[i]! = unpack 275 9 (T i)

theorem enumQ : EnumFacts mcl3QGens mcl3QCert EQ.N EQ.T := enum_of (ps := mcl3Keys) (fuel := 800)
  (bindE bindQ nums.2.1 gens.1) (fun k hk => by
    rw [Nat.eq_of_beq_eq_true nums.2.1] at hk
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gens.1 k hk)]
    exact pF (by omega)) EQ.ok hps EQ.keys (by rw [Nat.eq_of_beq_eq_true nums.1]; omega)

theorem pGA : ∀ k < EA.ng, permB 275 9 (EA.G k) = true := fun k hk => by
  rw [Nat.eq_of_beq_eq_true nums.2.2.2.1] at hk
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gens.2.1 k hk)]
  exact pF (by omega)

theorem enumA : EnumFacts mcl3CAGens mcl3CACert EA.N EA.T := enum_of (ps := mcl3Keys) (fuel := 29300)
  (bindE bindCA nums.2.2.2.1 gens.2.1) pGA EA.ok hps EA.keys
  (by rw [Nat.eq_of_beq_eq_true nums.2.2.1]; omega)

theorem enumO : EnumFacts mcl3OGens mcl3OCert EO.N EO.T := enum_of (ps := mcl3Keys) (fuel := 300)
  (bindE bindO nums.2.2.2.2.2.1 gens.2.2.1) (fun k hk => by
    rw [Nat.eq_of_beq_eq_true nums.2.2.2.2.2.1] at hk
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gens.2.2.1 k hk)]
    exact pF (by omega)) EO.ok hps EO.keys (by rw [Nat.eq_of_beq_eq_true nums.2.2.2.2.1]; omega)

theorem enumB : EnumFacts mcl3CBGens mcl3CBCert EB.N EB.T := enum_of (ps := mcl3Keys) (fuel := 1100)
  (bindE bindCB nums.2.2.2.2.2.2.2 gens.2.2.2) (fun k hk => by
    rw [Nat.eq_of_beq_eq_true nums.2.2.2.2.2.2.2] at hk
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gens.2.2.2 k hk)]
    exact pF (by omega)) EB.ok hps EB.keys (by rw [Nat.eq_of_beq_eq_true nums.2.2.2.2.2.2.1]; omega)

theorem permEA : ∀ i < EA.N, permB 275 9 (EA.T i) = true := fun i hi =>
  permB_of_pp (CFSG.KC.BfsPin.PP_pts EA.ok pGA i hi)

theorem lines_ok : linesOK3 3 729 148 275 mcl3QGens mcl3Keys mcl3QCert mcl3Lines = true := by
  obtain ⟨h1, h2, h3⟩ := enumQ
  have hN := Nat.eq_of_beq_eq_true nums.1
  rw [hN] at h2 h3
  have hl := lines
  rw [hN] at hl
  exact linesOK3_of szOK' h1 h2 h3 (fun i hi => permsOf EQ.perm i (by rw [hN]; exact hi)) bindL hl

theorem siftQ_ok : allLt mcl3QGens.size
    (fun l => siftA 275 PairMcL.levels PairMcL.baseArr 0 mcl3QGens[l]!) = true := by
  rw [allLt_iff]
  intro l hl
  rw [bindQ.1] at hl
  rw [bindQ.2 l hl]
  exact siftP (Orb.allN_iff.1 siftQ l hl : siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (F (0 + l)) = true)

theorem trans_ok : transOK2 148 275 mcl3Trans mcl3Lines mcl3Lines mcl3Rec PairMcL.levels
    PairMcL.baseArr = true :=
  transOK2_of szOK' bindH bindL (fun c hc => pF (by omega)) bindL (fun j hj => pF (by omega))
    (by decide +kernel)
    (fun j hj => by rw [bindH.2 j hj]; exact siftP (Orb.allN_iff.1 siftH j hj)) trans

theorem rec_ok : allLt 148 (fun j => decide (mcl3Rec.getD j 0 < 2)) = true := by
  rw [allLt_iff]
  have h : ∀ j < 148, mcl3Rec.getD j 0 < 2 := by decide +kernel
  intro j hj
  exact decide_eq_true (h j hj)

theorem hx0 : mcl3Lines[0]! = unpack 275 9 (F 4) := bindL.2 0 (by norm_num)

theorem hx1 : mcl3Lines[1]! = unpack 275 9 (F 5) := bindL.2 1 (by norm_num)

theorem permMA : ∀ j < 16, permB 275 9 (MA.S j) = true := fun j hj =>
  permB_of_pp (pp_of_permOK szOK' (Orb.allN_iff.1 permA j hj))

theorem permMB : ∀ j < 12, permB 275 9 (MB.S j) = true := fun j hj =>
  permB_of_pp (pp_of_permOK szOK' (Orb.allN_iff.1 permB' j hj))

theorem chainA_ok : caseChainOK2P 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3ChainAWords
    mclStrongArrs[0]! mclStrongArrs[1]! = true := by
  have hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 16 dA = mcl3ChainAWords := by
    decide +kernel
  have hc := rawChainK_sound (chunks := 1) bindsA MA.head MA.hl (by decide +kernel) MA.hs
  rw [hW] at hc
  unfold caseChainOK2P
  rw [hc, bindsA.2.2.2.2.1 0 (by norm_num), bindsA.2.2.2.2.1 1 (by norm_num),
    McLK.mclStrongArrs_get 0 (by norm_num), McLK.mclStrongArrs_get 1 (by norm_num),
    ← Nat.eq_of_beq_eq_true heads.1, ← Nat.eq_of_beq_eq_true heads.2.1,
    eqA_unpack' szOK' (permMA 0 (by norm_num)) (permMA 0 (by norm_num)),
    eqA_unpack' szOK' (permMA 1 (by norm_num)) (permMA 1 (by norm_num)), Nat.beq_refl,
    Nat.beq_refl]
  rfl

theorem chainB_ok : caseChainOK2P 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3ChainBWords
    mclStrongArrs[0]! mclStrongArrs[1]! = true := by
  have hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 dB = mcl3ChainBWords := by
    decide +kernel
  have hc := rawChainK_sound (chunks := 1) bindsB MB.head MB.hl (by decide +kernel) MB.hs
  rw [hW] at hc
  unfold caseChainOK2P
  rw [hc, bindsB.2.2.2.2.1 0 (by norm_num), bindsB.2.2.2.2.1 1 (by norm_num),
    McLK.mclStrongArrs_get 0 (by norm_num), McLK.mclStrongArrs_get 1 (by norm_num),
    ← Nat.eq_of_beq_eq_true heads.2.2.1, ← Nat.eq_of_beq_eq_true heads.2.2.2,
    eqA_unpack' szOK' (permMB 0 (by norm_num)) (permMB 0 (by norm_num)),
    eqA_unpack' szOK' (permMB 1 (by norm_num)) (permMB 1 (by norm_num)), Nat.beq_refl,
    Nat.beq_refl]
  rfl

theorem branchIdx_le {LR TR : ℕ → ℕ} {BP X : ℕ} {XP : ℕ → ℕ} {rels : List (ℕ × ℕ × ℕ)}
    {NE : ℕ} {EP ES : ℕ → ℕ} {nb q : ℕ}
    (h : ptailBranchIdxK 275 9 LR TR BP X XP rels NE EP ES nb q = true) :
    ptailBranchK 275 9 LR TR BP X XP rels NE EP nb q = true := by
  unfold ptailBranchIdxK at h
  unfold ptailBranchK
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (ptailIdxK_le _ _ _ h1)

theorem repA_ok : ∀ j < 1, repBranchK 275 9 MA.LR MA.TR MA.BP (F 4) (pw 275 9 (F 4)) mcl3RelsA
    EA.N EA.T 10 (RBA j) = true := by
  intro j hj
  obtain rfl : j = 0 := by omega
  have h := repA0
  unfold repA at h
  unfold repBranchK
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, branchIdx_le h.2⟩

theorem repB_ok : ∀ j < 3, repBranchK 275 9 MB.LR MB.TR MB.BP (F 5) (pw 275 9 (F 5)) mcl3RelsB
    EB.N EB.T 10 (RBB j) = true := by
  intro j hj
  have h : repB (RBB j) = true := by
    interval_cases j
    exacts [repB0, repB1, repB2]
  unfold repB at h
  unfold repBranchK
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, branchIdx_le h.2⟩

theorem hcA : rawChainOK 275 (mcl3ChainAArrs.extract 0 2) mcl3ChainAArrs mcl3ChainABaseArr
    mcl3ChainAWords 1 = true := by
  have hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 16 dA = mcl3ChainAWords := by
    decide +kernel
  have hc := rawChainK_sound (chunks := 1) bindsA MA.head MA.hl (by decide +kernel) MA.hs
  rw [hW] at hc
  exact hc

theorem hcB : rawChainOK 275 (mcl3ChainBArrs.extract 0 2) mcl3ChainBArrs mcl3ChainBBaseArr
    mcl3ChainBWords 1 = true := by
  have hW : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 dB = mcl3ChainBWords := by
    decide +kernel
  have hc := rawChainK_sound (chunks := 1) bindsB MB.head MB.hl (by decide +kernel) MB.hs
  rw [hW] at hc
  exact hc

theorem centA_ok : centOKP 3 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3Lines[0]! mcl3RelsA
    mcl3CAGens mcl3Keys mcl3CACert 29160 = true := by
  obtain ⟨h1, h2, h3⟩ := enumA
  have hN := Nat.eq_of_beq_eq_true nums.2.2.1
  rw [hx0, ← hN]
  exact centOKP_of_orbS szOK' bindsA permA MA.hl (k := 2) (by simp [mcl3ChainAArrs])
    (by decide +kernel) (by norm_num) hcA (pF (by norm_num)) relsA bindCA commA
    (fun k hk => siftA_of_siftOK bindsA permA MA.hl (Orb.allN_iff.1 siftCA k hk)) hps h1 h2 h3
    permEA (by norm_num) repA_ok (by rw [Nat.eq_of_beq_eq_true rc.1]; exact Orb.allN_iff.1 kOrbA)

theorem normal_ok : normalOKP 3 275 mcl3CAGens mcl3OGens mcl3Keys mcl3CACert mcl3OCert 243
    PairMcL.levels PairMcL.baseArr = true := by
  obtain ⟨-, a2, a3⟩ := enumA
  obtain ⟨o1, o2, o3⟩ := enumO
  exact normalOKP_of szOK' o1 o2 o3 (permsOf EO.perm) a2 a3 permEA bindCA
    (fun k hk => pF (by omega)) bindO (fun l hl => pF (by omega))
    (fun l hl => siftP (Orb.allN_iff.1 siftO l hl)) (Nat.eq_of_beq_eq_true nums.2.2.2.2.1) normal

theorem centB_ok : centOKP 3 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3Lines[1]! mcl3RelsB
    mcl3CBGens mcl3Keys mcl3CBCert 972 = true := by
  obtain ⟨h1, h2, h3⟩ := enumB
  have hN := Nat.eq_of_beq_eq_true nums.2.2.2.2.2.2.1
  rw [hx1, ← hN]
  exact centOKP_of_orbS szOK' bindsB permB' MB.hl (k := 2) (by simp [mcl3ChainBArrs])
    (by decide +kernel) (by norm_num) hcB (pF (by norm_num)) relsB bindCB commB
    (fun k hk => siftA_of_siftOK bindsB permB' MB.hl (Orb.allN_iff.1 siftCB k hk)) hps h1 h2 h3
    (permsOf EB.perm) (by norm_num) repB_ok
    (by rw [Nat.eq_of_beq_eq_true rc.2]; exact Orb.allN_iff.1 kOrbB)

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.Schreier in
open Certificates in
theorem facts :
    (linesOK3 3 729 148 275 mcl3QGens mcl3Keys mcl3QCert mcl3Lines = true ∧
      allLt mcl3QGens.size (fun l => siftA 275 PairMcL.levels PairMcL.baseArr 0 mcl3QGens[l]!) =
        true ∧
      transOK2 148 275 mcl3Trans mcl3Lines mcl3Lines mcl3Rec PairMcL.levels PairMcL.baseArr =
        true ∧
      allLt 148 (fun j => decide (mcl3Rec.getD j 0 < 2)) = true) ∧
    (caseChainOK2P 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3ChainAWords mclStrongArrs[0]!
        mclStrongArrs[1]! = true ∧
      centOKP 3 275 mcl3ChainAArrs mcl3ChainABaseArr mcl3Lines[0]! mcl3RelsA mcl3CAGens
        mcl3Keys mcl3CACert 29160 = true ∧
      normalOKP 3 275 mcl3CAGens mcl3OGens mcl3Keys mcl3CACert mcl3OCert 243 PairMcL.levels
        PairMcL.baseArr = true) ∧
    (caseChainOK2P 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3ChainBWords mclStrongArrs[0]!
        mclStrongArrs[1]! = true ∧
      centOKP 3 275 mcl3ChainBArrs mcl3ChainBBaseArr mcl3Lines[1]! mcl3RelsB mcl3CBGens
        mcl3Keys mcl3CBCert 972 = true) :=
  ⟨⟨lines_ok, siftQ_ok, trans_ok, rec_ok⟩, ⟨chainA_ok, centA_ok, normal_ok⟩,
    ⟨chainB_ok, centB_ok⟩⟩

end CertificateChecks.KernelK426

end
