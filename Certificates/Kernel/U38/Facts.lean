module

public import Certificates.Kernel.U38.Checks
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import Certificates.Data.KD4BU38.Data
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.K426K
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.Certificates.Native
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes
open CFSG.Monster.B.Co2 (allLt_iff)

theorem arrF {k : ℕ} (hk : k < 28) : pgu38Arr k = unpack 513 10 (UF.F k) := by
  rw [pgu38Arr, UF.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound UF.all k hk

theorem arrH {k : ℕ} (hk : k < 25) : permArr k = unpack 513 10 (UH.F k) := by
  rw [permArr, UH.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound UH.all k hk

theorem pF {k : ℕ} (hk : k < 28) : permB 513 10 (UF.F k) = true := Orb.allN_iff.1 permF k hk

theorem pH {k : ℕ} (hk : k < 25) : permB 513 10 (UH.F k) = true := Orb.allN_iff.1 permH k hk

theorem getOfFn' {m j : ℕ} {f : ℕ → Array ℕ} (hj : j < m) :
    (Array.ofFn fun i : Fin m => f i.val)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem gq {j : ℕ} (hj : j < 3) : pgu38SylowGens[j]! = unpack 513 10 (UF.F j) := by
  rw [pgu38SylowGens, getOfFn' hj]
  exact arrF (by omega)

theorem reps {j : ℕ} (hj : j < 10) : pgu38ClassReps[j]! = unpack 513 10 (UF.F (3 + j)) := by
  rw [pgu38ClassReps, getOfFn' (f := fun j => pgu38Arr (3 + j)) hj]
  exact arrF (by omega)

theorem repConj {j : ℕ} (hj : j < 10) : pgu38RepConj[j]! = unpack 513 10 (UF.F (13 + j)) := by
  rw [pgu38RepConj, getOfFn' (f := fun j => pgu38Arr (13 + j)) hj]
  exact arrF (by omega)

theorem frobConj {j : ℕ} (hj : j < 5) : pgu38FrobConj[j]! = unpack 513 10 (UF.F (23 + j)) := by
  rw [pgu38FrobConj, getOfFn' (f := fun j => pgu38Arr (23 + j)) hj]
  exact arrF (by omega)

theorem gO {j : ℕ} (hj : j < 9) : gensO[j]! = unpack 513 10 (UH.F j) := by
  rw [gensO, getOfFn' hj]
  exact arrH (by omega)

theorem strong3_get {j : ℕ} (hj : j < 11) :
    strong3[j]! = permArr (if j < 7 then j else 14 + j) := by
  interval_cases j <;> rfl

theorem binds : Binds 513 10 UX.S 11 4 UX.BP strong3 base3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, rfl, fun j hj => ?_, rfl,
    fun t ht => by interval_cases t <;> decide +kernel⟩
  rw [strong3_get hj]
  split_ifs with h
  · rw [arrH (by omega), Nat.eq_of_beq_eq_true (Orb.allN_iff.1 chainX.1 j h)]
  · have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 chainX.2 (j - 7) (by omega))
    have e1 : Nat.add 7 (j - 7) = j := by change 7 + (j - 7) = j; omega
    have e2 : Nat.add 21 (j - 7) = 14 + j := by change 21 + (j - 7) = 14 + j; omega
    rw [e1, e2] at e
    rw [arrH (by omega), e]

theorem siftX {G : ℕ} (h : siftOK 513 10 4 UX.LR UX.TRI UX.BP G = true) :
    pgu38SiftX (unpack 513 10 G) = true :=
  siftA_of_siftOK binds permX UX.hl h

theorem hidx {r : ℕ} (hr : r < 5) :
    pgu38RepIdx[r]! = [7, 8, 2, 0, 3].getD r 0 ∧ [7, 8, 2, 0, 3].getD r 0 < 10 := by
  interval_cases r <;> exact ⟨rfl, by decide⟩

theorem hps : ∀ p ∈ pgu38Key, p < 513 := by decide

theorem enumQ : enumOK 513 pgu38SylowGens pgu38Key (pgu38SylowEnum ()) = true ∧
    (pgu38SylowEnum ()).pts.size = UQ.N ∧
    ∀ i < UQ.N, (pgu38SylowEnum ()).pts[i]! = unpack 513 10 (UQ.T i) := by
  have hng := Nat.eq_of_beq_eq_true nums.2
  have hb : BindA 513 10 pgu38SylowGens UQ.ng UQ.G := by
    rw [hng]
    refine ⟨rfl, fun j hj => ?_⟩
    rw [gq hj, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gensQ j hj)]
  have hp : ∀ k < UQ.ng, permB 513 10 (UQ.G k) = true := fun k hk => by
    rw [hng] at hk
    rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gensQ k hk)]
    exact pF (by omega)
  exact enum_of (ps := pgu38Key) (fuel := 300) hb hp UQ.ok hps UQ.keys
    (by rw [Nat.eq_of_beq_eq_true nums.1]; omega)

theorem hw : szOK 513 10 = true := szOK'

theorem hid : permB 513 10 (pidn 513 10) = true := permB_id hw

theorem pg7i : permB 513 10 (pinvS 513 10 (mask 10) (UH.F 7)) = true :=
  permB_pinvS hw (pH (by norm_num))

theorem invG7 : invCand 513 gensO[7]! = unpack 513 10 (pinvS 513 10 (mask 10) (UH.F 7)) := by
  rw [gO (by norm_num), inv_unpack hw (pH (by norm_num))]

theorem sylowSift : allLt 3 (fun j => pgu38SiftX (compA 513 pgu38SylowGens[j]!
    (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) pgu38SylowExp[j]!))) = true := by
  rw [allLt_iff]
  intro j hj
  have he : pgu38SylowExp[j]! = [1, 2, 0].getD j 0 := by interval_cases j <;> rfl
  rw [gq hj, invG7, pow_unpack hw pg7i, he, comp_unpack hw (pF (by omega)) (permB_ppow hw pg7i _)]
  exact siftX (Orb.allN_iff.1 kSylow j hj)

theorem classOK : pgu38ClassCheck (pgu38SylowEnum ()).pts = true := by
  obtain ⟨-, hN, hT⟩ := enumQ
  have hN' : (pgu38SylowEnum ()).pts.size = 243 := by rw [hN, Nat.eq_of_beq_eq_true nums.1]
  have hT' : ∀ i < 243, (pgu38SylowEnum ()).pts[i]! = unpack 513 10 (UQ.T i) := fun i hi =>
    hT i (by rw [Nat.eq_of_beq_eq_true nums.1]; exact hi)
  have hpT : ∀ i < 243, permB 513 10 (UQ.T i) = true := fun i hi =>
    Orb.allN_iff.1 UQ.perm i (by rw [Nat.eq_of_beq_eq_true nums.1]; exact hi)
  unfold pgu38ClassCheck
  rw [allLt_iff, hN']
  intro i hi
  have hc := Orb.allN_iff.1 kClass i hi
  unfold classAt at hc
  rw [hT' i hi, CFSG.KC.Misc.ArrEnum.pow_unpack hw (hpT i hi), CFSG.KC.BfsPin.idA_eq hw,
    eqA_unpack hw (permB_ppow hw (hpT i hi) 3) hid, eqA_unpack hw (hpT i hi) hid]
  rw [Bool.or_eq_true] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl hc
  · right
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have h1' : CW.getD i 0 / 16 < 243 := by simpa [Nat.blt_eq] using h1
    have h2' : CW.getD i 0 % 16 < 10 := by simpa [Nat.blt_eq] using h2
    rw [List.any_eq_true]
    refine ⟨CW.getD i 0 / 16, List.mem_range.2 h1', ?_⟩
    rw [List.any_eq_true]
    refine ⟨CW.getD i 0 % 16, List.mem_range.2 h2', ?_⟩
    rw [hT' _ h1', conj_unpack hw (hpT _ h1') (hpT i hi), reps h2',
      eqA_unpack hw (permB_pcomp hw (hpT _ h1') (permB_pcomp hw (hpT i hi)
        (permB_pinvS hw (hpT _ h1')))) (pF (by omega))]
    exact h3

theorem repsOK : allLt 10 (fun j => validA 513 pgu38ClassReps[j]! && validA 513 pgu38RepConj[j]! &&
    pgu38SiftX (compA 513 pgu38RepConj[j]!
      (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) pgu38RepConjExp[j]!)) &&
    (List.range 5).any fun r => decide (pgu38RepIdx[r]! < 10) &&
      eqA 513 (conjA 513 pgu38RepConj[j]! pgu38ClassReps[j]!)
        pgu38ClassReps[pgu38RepIdx[r]!]!) = true := by
  rw [allLt_iff]
  intro j hj
  have hr := Orb.allN_iff.1 kReps j hj
  unfold repAt at hr
  rw [Bool.and_eq_true, Bool.and_eq_true] at hr
  obtain ⟨⟨hs, hr5⟩, he⟩ := hr
  have hr5' : RW.getD j 0 < 5 := by simpa [Nat.blt_eq] using hr5
  have hex : pgu38RepConjExp[j]! = [0, 2, 0, 0, 0, 2, 1, 0, 0, 1].getD j 0 := by
    interval_cases j <;> rfl
  have p3 : permB 513 10 (UF.F (3 + j)) = true := pF (by omega)
  have p13 : permB 513 10 (UF.F (13 + j)) = true := pF (by omega)
  rw [reps hj, repConj hj, CFSG.KC.BfsPin.validA_unpack p3, CFSG.KC.BfsPin.validA_unpack p13,
    invG7, pow_unpack hw pg7i, hex, comp_unpack hw p13 (permB_ppow hw pg7i _), siftX hs,
    conj_unpack hw p13 p3]
  simp only [Bool.true_and]
  rw [List.any_eq_true]
  refine ⟨RW.getD j 0, List.mem_range.2 hr5', ?_⟩
  obtain ⟨hi1, hi2⟩ := hidx hr5'
  rw [hi1, reps hi2, eqA_unpack hw (permB_pcomp hw p13 (permB_pcomp hw p3 (permB_pinvS hw p13)))
    (pF (by omega)), decide_eq_true hi2]
  exact he

theorem frobOK : allLt 5 (fun r => decide (pgu38RepIdx[r]! < 10) &&
    validA 513 pgu38FrobConj[r]! &&
    pgu38SiftX (compA 513 pgu38FrobConj[r]!
      (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) pgu38FrobConjExp[r]!)) &&
    (eqA 513 (conjA 513 pgu38FrobConj[r]! (conjA 513 gensO[8]! pgu38ClassReps[pgu38RepIdx[r]!]!))
        pgu38ClassReps[pgu38RepIdx[r]!]! ||
      eqA 513 (conjA 513 pgu38FrobConj[r]! (conjA 513 gensO[8]! pgu38ClassReps[pgu38RepIdx[r]!]!))
        (invCand 513 pgu38ClassReps[pgu38RepIdx[r]!]!))) = true := by
  rw [allLt_iff]
  intro r hr
  have hf := Orb.allN_iff.1 kFrob r hr
  unfold frobAt at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨hs, he⟩ := hf
  obtain ⟨hi1, hi2⟩ := hidx hr
  have hex : pgu38FrobConjExp[r]! = [2, 2, 2, 1, 2].getD r 0 := by interval_cases r <;> rfl
  have p23 : permB 513 10 (UF.F (23 + r)) = true := pF (by omega)
  have pR : permB 513 10 (UF.F (3 + [7, 8, 2, 0, 3].getD r 0)) = true := pF (by omega)
  have p8 : permB 513 10 (UH.F 8) = true := pH (by norm_num)
  have pc : permB 513 10 (pcomp 513 10 (mask 10) (UH.F 8)
      (pcomp 513 10 (mask 10) (UF.F (3 + [7, 8, 2, 0, 3].getD r 0)) (pinvS 513 10 (mask 10) (UH.F 8))))
      = true := permB_pcomp hw p8 (permB_pcomp hw pR (permB_pinvS hw p8))
  rw [hi1, reps hi2, frobConj hr, invG7, gO (show 8 < 9 by norm_num), decide_eq_true hi2,
    CFSG.KC.BfsPin.validA_unpack p23, pow_unpack hw pg7i, hex,
    comp_unpack hw p23 (permB_ppow hw pg7i _), siftX hs, conj_unpack hw p8 pR,
    conj_unpack hw p23 pc, inv_unpack hw pR,
    eqA_unpack hw (permB_pcomp hw p23 (permB_pcomp hw pc (permB_pinvS hw p23))) pR,
    eqA_unpack hw (permB_pcomp hw p23 (permB_pcomp hw pc (permB_pinvS hw p23)))
      (permB_pinvS hw pR)]
  simp only [Bool.true_and]
  exact he

theorem lastOK : pgu38SiftX (CFSG.Monster.B.Mathieu.powArr 513 gensO[7]! 3) = true ∧
    pgu38SiftX (compA 513 (conjA 513 gensO[8]! gensO[7]!)
      (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) 2)) = true ∧
    pgu38SiftX (compA 513 (conjInvA 513 gensO[8]! gensO[7]!)
      (CFSG.Monster.B.Mathieu.powArr 513 (invCand 513 gensO[7]!) 2)) = true := by
  have p7 : permB 513 10 (UH.F 7) = true := pH (by norm_num)
  have p8 : permB 513 10 (UH.F 8) = true := pH (by norm_num)
  obtain ⟨k1, k2, k3⟩ := kLast
  refine ⟨?_, ?_, ?_⟩
  · rw [gO (by norm_num), pow_unpack hw p7]
    exact siftX k1
  · rw [invG7, gO (show 7 < 9 by norm_num), gO (show 8 < 9 by norm_num), conj_unpack hw p8 p7,
      pow_unpack hw pg7i,
      comp_unpack hw (permB_pcomp hw p8 (permB_pcomp hw p7 (permB_pinvS hw p8)))
        (permB_ppow hw pg7i 2)]
    exact siftX k2
  · rw [invG7, gO (show 7 < 9 by norm_num), gO (show 8 < 9 by norm_num), conjInv_unpack hw p8 p7,
      pow_unpack hw pg7i,
      comp_unpack hw (permB_pcomp hw (permB_pinvS hw p8) (permB_pcomp hw p7 p8))
        (permB_ppow hw pg7i 2)]
    exact siftX k3

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.PGU38Classes CFSG.RankThree.PartTwo.Sec4.Item434U38
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Mathieu in
open Certificates in
theorem facts :
    (enumOK 513 pgu38SylowGens pgu38Key (pgu38SylowEnum ()) = true ∧
      (pgu38SylowEnum ()).pts.size = 243) ∧
    allLt 3 (fun j => pgu38SiftX (compA 513 pgu38SylowGens[j]!
      (powArr 513 (invCand 513 gensO[7]!) pgu38SylowExp[j]!))) = true ∧
    pgu38ClassCheck (pgu38SylowEnum ()).pts = true ∧
    allLt 10 (fun j => validA 513 pgu38ClassReps[j]! && validA 513 pgu38RepConj[j]! &&
      pgu38SiftX (compA 513 pgu38RepConj[j]!
        (powArr 513 (invCand 513 gensO[7]!) pgu38RepConjExp[j]!)) &&
      (List.range 5).any fun r => decide (pgu38RepIdx[r]! < 10) &&
        eqA 513 (conjA 513 pgu38RepConj[j]! pgu38ClassReps[j]!)
          pgu38ClassReps[pgu38RepIdx[r]!]!) = true ∧
    allLt 5 (fun r => decide (pgu38RepIdx[r]! < 10) && validA 513 pgu38FrobConj[r]! &&
      pgu38SiftX (compA 513 pgu38FrobConj[r]!
        (powArr 513 (invCand 513 gensO[7]!) pgu38FrobConjExp[r]!)) &&
      (eqA 513 (conjA 513 pgu38FrobConj[r]! (conjA 513 gensO[8]! pgu38ClassReps[pgu38RepIdx[r]!]!))
          pgu38ClassReps[pgu38RepIdx[r]!]! ||
        eqA 513 (conjA 513 pgu38FrobConj[r]! (conjA 513 gensO[8]! pgu38ClassReps[pgu38RepIdx[r]!]!))
          (invCand 513 pgu38ClassReps[pgu38RepIdx[r]!]!))) = true ∧
    pgu38SiftX (powArr 513 gensO[7]! 3) = true ∧
    pgu38SiftX (compA 513 (conjA 513 gensO[8]! gensO[7]!) (powArr 513 (invCand 513 gensO[7]!) 2)) =
      true ∧
    pgu38SiftX (compA 513 (conjInvA 513 gensO[8]! gensO[7]!)
      (powArr 513 (invCand 513 gensO[7]!) 2)) = true := by
  obtain ⟨e1, e2, -⟩ := enumQ
  refine ⟨⟨e1, ?_⟩, sylowSift, classOK, repsOK, frobOK, lastOK⟩
  rw [e2, Nat.eq_of_beq_eq_true nums.1]

end CertificateChecks.KernelU38

end
