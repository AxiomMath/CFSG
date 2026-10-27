module

public import Certificates.Kernel.Fi23R.Group
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24Orders
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24OrdersData
public import Certificates.Kernel.Fi23O4.Chk
import Certificates.Kernel.Fi23R.Fact2075
import Certificates.Kernel.Fi23S.Fact1014
import Certificates.Kernel.Fi23M.Keys
import CFSG.Certificates.Kernel.B32Sound
import CFSG.Certificates.Kernel.Spor.TextAtSound
import CFSG.Certificates.Kernel.RankThree.F2Perm
import CFSG.Certificates.Kernel.J4FixCSoundPrelude
import CFSG.Sporadic.Schreier.J4SSylow
import CFSG.Certificates.Kernel.J4FixCSoundBase1
import Certificates.Data.Kernel.J4FixC
import CFSG.Certificates.Kernel.SporSch.J4SColsSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Sporadic.Schreier.J4SBinary
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import CFSG.Sporadic.M23.Transitivity
import CFSG.Sporadic.Schreier.J4SKCent
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.SporSch.J4S.NoCP
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23O4

open CFSG.KC.Enum CFSG.KC.Fi23R CFSG.KC.B32 CFSG.KC.Fi23O4 CFSG.KD.Fi23K CFSG.KD.Fi23O4
open CertificateChecks.KernelFi23R
open CFSG.ComponentClassification.RankTwoSporadic.Cert (slpStep slpRegs slpIdxOK slpOK
  decodePairs getElem!_push_of_lt getElem!_push_size powA rep_powA commA_iff)
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime (fi23FourCheck fi23FourSlp fi23FourX
  fi23FourZ)

abbrev CRep (t : Array ℕ) (p : Pt) : Prop := CFSG.Monster.B.Co2.Rep 31671 t p

@[expose] def Inv (regs : Array (Array ℕ)) (ws : Array (List ℕ)) : Prop :=
  regs.size = ws.size ∧ ∀ k < regs.size, CRep regs[k]! (wp ws[k]!) ∧ ∀ c ∈ ws[k]!, okL c

theorem inv_step {regs : Array (Array ℕ)} {ws : Array (List ℕ)} (h : Inv regs ws) {ij : ℕ × ℕ}
    (hi : ij.1 < regs.size) (hj : ij.2 < regs.size) :
    Inv (slpStep 31671 regs ij) (ws.push (ws[ij.2]! ++ ws[ij.1]!)) := by
  obtain ⟨hs, hr⟩ := h
  refine ⟨by simp [slpStep, hs], fun k hk => ?_⟩
  simp only [slpStep, Array.size_push] at hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
  · rw [slpStep, getElem!_push_of_lt hk, getElem!_push_of_lt (hs ▸ hk)]
    exact hr k hk
  · rw [slpStep, getElem!_push_size, hs, getElem!_push_size]
    obtain ⟨r1, o1⟩ := hr _ hi
    obtain ⟨r2, o2⟩ := hr _ hj
    refine ⟨?_, ok_append o2 o1⟩
    rw [wp_append]
    exact CFSG.Monster.B.Co2.rep_compA r1 r2

theorem inv_fold : ∀ (prog : List (ℕ × ℕ)) (regs : Array (Array ℕ)) (ws : Array (List ℕ)),
    Inv regs ws → slpIdxOK regs.size prog = true →
      Inv (prog.foldl (slpStep 31671) regs)
        (prog.foldl (fun ws ij => ws.push (ws[ij.2]! ++ ws[ij.1]!)) ws)
  | [], _, _, h, _ => h
  | ij :: l, regs, ws, h, hok => by
    simp only [slpIdxOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hi, hj⟩, hl⟩ := hok
    rw [List.foldl_cons, List.foldl_cons]
    exact inv_fold l _ _ (inv_step h hi hj) (by simpa [slpStep] using hl)

theorem size_slpWords (b : Array (List ℕ)) :
    ∀ prog : List (ℕ × ℕ), (slpWords b prog).size = b.size + prog.length
  | [] => rfl
  | ij :: l => by
    unfold slpWords
    rw [List.foldl_cons]
    have := size_slpWords (b.push (b[ij.2]! ++ b[ij.1]!)) l
    unfold slpWords at this
    rw [this, Array.size_push, List.length_cons]
    omega

theorem wp_one (c : ℕ) : wp [c] = lp c := by rw [wp_cons, wp_nil, one_mul]

theorem ok_one {c : ℕ} (h : okL c) : ∀ d ∈ [c], okL d := fun d hd => by
  rw [List.mem_singleton] at hd
  exact hd ▸ h

theorem prog_idx : slpIdxOK 4 prog = true := by decide +kernel

theorem facts' : CFSG.KS.Text.asciiK S.chars = true ∧ prog.length = 176 ∧
    fourK G words[18]! words[179]! = true := by
  have h := facts_ok
  unfold facts at h
  rw [CFSG.KC.J4FixC.bAnd_eq, CFSG.KC.J4FixC.bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩

theorem four_facts {x z : List ℕ} (h : fourK G x z = true) :
    eqB G x [43] = true ∧ eqB G (x ++ z) (z ++ x) = true ∧ eqB G (powW 4 z) [] = true ∧
      eqB G (z ++ z) [] = false := by
  unfold fourK at h
  rw [CFSG.KC.J4FixC.bAnd_eq, CFSG.KC.J4FixC.bAnd_eq, CFSG.KC.J4FixC.bAnd_eq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

theorem decode_eq : decodePairs fi23FourSlp = prog := by
  rw [S.eq]
  exact CFSG.KS.B32.decodePairs_ofList (CFSG.KS.Text.asciiK_spec facts'.1)

theorem inv_base {A B : Array ℕ} (hA : CRep A aP) (hB : CRep B bP) :
    Inv (#[A, B] ++ #[A, B].map (CFSG.Monster.B.Co2.Native.invCand 31671)) base := by
  have hAi := CFSG.RankThree.Native.F2.rep_invCand hA
  have hBi := CFSG.RankThree.Native.F2.rep_invCand hB
  rw [aP_inv] at hAi
  have e : #[A, B] ++ #[A, B].map (CFSG.Monster.B.Co2.Native.invCand 31671) =
      #[A, B, CFSG.Monster.B.Co2.Native.invCand 31671 A,
        CFSG.Monster.B.Co2.Native.invCand 31671 B] := by simp
  rw [e]
  refine ⟨rfl, fun k hk => ?_⟩
  have hk4 : k < 4 := hk
  have o39 : okL 39 := Or.inl rfl
  have o40 : okL 40 := Or.inr (Or.inl rfl)
  have o41 : okL 41 := Or.inr (Or.inr (Or.inl rfl))
  have b0 : base[0]! = [39] := rfl
  have b1 : base[1]! = [40] := rfl
  have b2 : base[2]! = [39] := rfl
  have b3 : base[3]! = [41] := rfl
  interval_cases k
  · exact ⟨by rw [b0, wp_one, lp_39]; exact hA, b0 ▸ ok_one o39⟩
  · exact ⟨by rw [b1, wp_one, lp_40]; exact hB, b1 ▸ ok_one o40⟩
  · exact ⟨by rw [b2, wp_one, lp_39]; exact hAi, b2 ▸ ok_one o39⟩
  · exact ⟨by rw [b3, wp_one, lp_41]; exact hBi, b3 ▸ ok_one o41⟩

theorem inv_regs {A B : Array ℕ} (hA : CRep A aP) (hB : CRep B bP) :
    Inv (slpRegs 31671 #[A, B] prog) words := by
  unfold slpRegs words slpWords
  refine inv_fold prog _ _ (inv_base hA hB) ?_
  have e : (#[A, B] ++ #[A, B].map (CFSG.Monster.B.Co2.Native.invCand 31671)).size = 4 := by simp
  rw [e]
  exact prog_idx

theorem rep_tab {z : ℤ} (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) {T : CFSG.Sporadic.Th.Native.Table}
    (hT : T = CFSG.Sporadic.Fi23.Native.genTables orbLit z) :
    CRep (T.map UInt32.toNat) (lp (regZ z)) := by
  have hs := (genTables_TR (z := z) (by omega) (by omega)).1
  have hr := rep_gen hz
  rw [← hT] at hs hr
  intro x
  have hx : x.val < T.size := by rw [hs]; exact x.2
  rw [getElem!_pos _ _ (by simpa using hx), Array.getElem_map, ← idx_eq _ x.2, ← hr x.val x.2]
  unfold CFSG.Sporadic.Th.Native.ap
  rw [getElem!_pos T x.val hx]

theorem rep_alpha : CRep (orbLit.alpha.map UInt32.toNat) aP := by
  have h := rep_tab (z := 1) (by decide) (T := orbLit.alpha) (by
    unfold CFSG.Sporadic.Fi23.Native.genTables
    rw [if_pos (Or.inl rfl)])
  have e : regZ 1 = 39 := rfl
  rwa [e, lp_39] at h

theorem rep_beta : CRep (orbLit.beta.map UInt32.toNat) bP := by
  have h := rep_tab (z := 2) (by decide) (T := orbLit.beta) (by
    unfold CFSG.Sporadic.Fi23.Native.genTables
    rw [if_neg (by decide), if_pos rfl])
  have e : regZ 2 = 40 := rfl
  rwa [e, lp_40] at h

theorem fixA_D {t : Array ℕ} (h : CRep t dP) :
    CFSG.ComponentClassification.RankTwoSporadic.RootCensus.fixA 31671 t = 3511 := by
  obtain ⟨-, -, h3, -⟩ := CertificateChecks.KernelFi23S.misc_facts
  rw [← h3, cntS_zero]
  unfold CFSG.ComponentClassification.RankTwoSporadic.RootCensus.fixA
  apply List.countP_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  have hw := wp_acts [43] (ok_one (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) i hi'
  rw [wp_one, lp_43] at hw
  rw [beq_iff_eq, fxW_iff, h.apply hi', hw]

theorem four_ok : fi23FourCheck fi23FourSlp fi23FourX fi23FourZ = true := by
  obtain ⟨-, hlen, h4⟩ := facts'
  obtain ⟨e1, e2, e3, e4⟩ := four_facts h4
  have hg : CFSG.ComponentClassification.RankTwoSporadic.Fi23.fi23Gens =
      #[orbLit.alpha.map UInt32.toNat, orbLit.beta.map UInt32.toNat] := by
    unfold CFSG.ComponentClassification.RankTwoSporadic.Fi23.fi23Gens
    rw [CFSG.KD.Fi23K.orbitData_eq']
  have hA := rep_alpha
  have hB := rep_beta
  unfold fi23FourCheck fi23FourX fi23FourZ
  rw [decode_eq, hg]
  generalize orbLit.alpha.map UInt32.toNat = A at hA ⊢
  generalize orbLit.beta.map UInt32.toNat = B at hB ⊢
  obtain ⟨hsz, hR⟩ := inv_regs hA hB
  have hws : words.size = 180 := by
    unfold words
    rw [size_slpWords, hlen]
    rfl
  rw [hws] at hsz
  obtain ⟨rx, ox⟩ := hR 18 (by omega)
  obtain ⟨rz, oz⟩ := hR 179 (by omega)
  have o43 : ∀ c ∈ [43], okL c := ok_one (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hxD : wp words[18]! = dP := by
    rw [wp_eq_of_eqB e1 ox o43, wp_one, lp_43]
  have hxz : wp words[179]! * wp words[18]! = wp words[18]! * wp words[179]! := by
    have := wp_eq_of_eqB e2 (ok_append ox oz) (ok_append oz ox)
    rwa [wp_append, wp_append] at this
  have hz4 : wp words[179]! ^ 4 = 1 := by
    have := wp_eq_of_eqB e3 (ok_powW oz 4) (fun _ h => absurd h List.not_mem_nil)
    rwa [wp_powW, wp_nil] at this
  have hz2 : wp words[179]! ^ 2 ≠ 1 := by
    intro h
    have ht : eqB G (words[179]! ++ words[179]!) [] = true := by
      unfold eqB
      rw [CFSG.KS.Raw.Orb.allN_iff]
      intro b hb
      have hb6 : b < 6 := hb
      have hw := wp_acts _ (ok_append oz oz) b (by omega)
      rw [wp_append, ← sq, h] at hw
      rw [Nat.beq_eq, ← hw]
      rfl
    rw [e4] at ht
    exact absurd ht (by decide)
  have hslp : slpOK 31671 #[A, B] prog = true := by
    unfold slpOK
    rw [Bool.and_eq_true]
    refine ⟨?_, by simpa using prog_idx⟩
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have hk2 : k < 2 := by simpa using hk
    interval_cases k
    · exact CFSG.RankThree.Native.F2.validA_of_rep hA
    · exact CFSG.RankThree.Native.F2.validA_of_rep hB
  rw [hxD] at rx
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨hslp, by omega⟩, by omega⟩, fixA_D rx⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA rx rx)
      CFSG.Monster.B.Co2.rep_idA).2 dP_sq
  · rw [← hxD] at rx
    exact (commA_iff rx rz).2 hxz.symm
  · exact (CFSG.Monster.B.Co2.eqA_iff (rep_powA rz 4) CFSG.Monster.B.Co2.rep_idA).2 hz4
  · cases he : CFSG.Monster.B.Co2.Native.eqA 31671 (powA 31671 (slpRegs 31671 #[A, B] prog)[179]! 2)
      (CFSG.Monster.B.Co2.Native.idA 31671)
    · rfl
    · exact absurd ((CFSG.Monster.B.Co2.eqA_iff (rep_powA rz 2) CFSG.Monster.B.Co2.rep_idA).1 he)
        hz2

end CertificateChecks.KernelFi23O4

end
