
module

public import Certificates.Kernel.SporSch.J4S.Odd
public import CFSG.Certificates.Kernel.SporSch.J4SSpanSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4Odd

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4Eta

theorem sc_eq {m : Nat} (h1 : 1 ≤ m) (h9 : m < 9) :
    sCols m = CFSG.KS.SporSch.C11.unpack11 (J4G1 (m - 1)) := by
  rw [← J4Orbits.g1_bind.2 (m - 1) (by omega)]
  interval_cases m <;> rfl

theorem pathApp_eq : ∀ (w : List Nat) (a : Nat), (∀ m ∈ w, 1 ≤ m ∧ m < 9) →
    pathApp w a = pathAppK w a
  | [], _, _ => rfl
  | m :: w, a, h => by
    have hm := h m List.mem_cons_self
    rw [pathApp, List.foldl_cons, ← pathApp, sc_eq hm.1 hm.2, CFSG.KS.SporSch.C11.app_eq]
    exact pathApp_eq w _ fun m' hm' => h m' (List.mem_cons_of_mem _ hm')

theorem pathVecs_eq (p : Nat × List (List Nat)) (h : ∀ w ∈ p.2, ∀ m ∈ w, 1 ≤ m ∧ m < 9) :
    pathVecs p = pvK p := by
  obtain ⟨a, ws⟩ := p
  rw [pathVecs]
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons, pathApp_eq w a (h w List.mem_cons_self),
      ih fun w' hw' => h w' (List.mem_cons_of_mem _ hw')]
    rfl

theorem allL_mem {L : List (Nat × List (List Nat))} {f : Nat × List (List Nat) → Bool} :
    List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(f p, ih)) L = true →
    ∀ p ∈ L, f p = true := by
  induction L with
  | nil => intro _ p hp; exact absurd hp List.not_mem_nil
  | cons q L ih =>
    intro h p hp
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · exact ih h2 p hp

theorem spanOK_of {vs : List Nat} (h : ∀ c < 2048, ∃ m < 2048, xorSub vs m = c) :
    spanOK vs = true := by
  rw [spanOK, List.all_eq_true]
  intro c hc
  obtain ⟨m, hm, e⟩ := h c (List.mem_range.1 hc)
  rw [List.contains_iff_mem, List.mem_map]
  exact ⟨m, List.mem_range.2 hm, e⟩

theorem rowJ_lt (P r : Nat) : rowJ rm P r < 2 ^ 112 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem hE : WfN eRows ∧ encN eRows = getN one J4EE 0 := by
  have h := ek
  obtain ⟨h1, h2⟩ := (bAnd_iff (canonJ pad (getN one J4EE 0)) _).1 h
  unfold eRows
  refine ofFn_enc J4Real.hK (fun i => ?_) h1 (fun i => Nat.eq_of_beq_eq_true (allN_spec h2 i i.isLt))
  rw [← Nat.eq_of_beq_eq_true (allN_spec h2 i i.isLt)]
  exact rowJ_lt _ _

theorem hU {l : Nat} (hl : l < 10) : WfN (CFSG.Sporadic.J4Schreier.selRows l) ∧ encN (CFSG.Sporadic.J4Schreier.selRows l) = getN one J4CP (10 + l) := by
  have h := allBlk_spec (J4US.all l hl) 0 Nat.zero_lt_one
  rw [show Nat.add (Nat.mul 1 l) 0 = l by simp] at h
  unfold uK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  unfold CFSG.Sporadic.J4Schreier.selRows
  refine ofFn_enc J4Real.hK (fun i => ?_) h1 (fun i => Nat.eq_of_beq_eq_true (allN_spec h2 i i.isLt))
  rw [← Nat.eq_of_beq_eq_true (allN_spec h2 i i.isLt)]
  exact rowJ_lt _ _

theorem commM_eq {l : Nat} (hl : l < 10) : commM commPairs[l]! = cmK l := by
  have hlen : l < commPairs.length := by rw [misc.2.2.2.2]; exact hl
  have hmem : commPairs[l]! ∈ commPairs := by
    rw [getElem!_pos commPairs l hlen]
    exact List.getElem_mem _
  have hp := misc.2.1 commPairs[l]! hmem
  have e : commPairs.getD l (0, 0) = commPairs[l]! := by
    rw [List.getD_eq_getElem?_getD, getElem!_pos commPairs l hlen, List.getElem?_eq_getElem hlen,
      Option.getD_some]
  rw [commM, cmK, e, J4Five.GC_eq hp.2, CFSG.KS.SporSch.C11.app_eq]
  generalize commPairs[l]! = p at hp ⊢
  cases p
  rfl

theorem hM {l : Nat} (hl : l < 10) :
    WfN (etaP (commM commPairs[l]!)).2 ∧ encN (etaP (commM commPairs[l]!)).2 = getN one J4CP l := by
  have e1 : prodSK c rm one (es (cmK l)) = getN one J4CP l := Nat.eq_of_beq_eq_true (allN_spec mk l hl)
  have h : PairOK (etaP (cmK l)) (prodFK c rm one (ef (cmK l))) (prodSK c rm one (es (cmK l))) :=
    etaP_ok (cmK l)
  rw [commM_eq hl]
  exact ⟨h.2.1, h.2.2.trans e1⟩

theorem certSum_ok : ∀ ls : List Nat, (∀ l ∈ ls, l < 10) →
    WfN (certSum (ls.map fun l => ((etaP (commM commPairs[l]!)).2, CFSG.Sporadic.J4Schreier.selRows l))) ∧
      encN (certSum (ls.map fun l => ((etaP (commM commPairs[l]!)).2, CFSG.Sporadic.J4Schreier.selRows l))) = csK ls
  | [], _ => hE
  | l :: ls, h => by
    have hl := h l List.mem_cons_self
    have ih := certSum_ok ls fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have m := mulRows_enc J4Real.hK (hM hl).1 (hU hl).1
    have x1 := xor_enc m.1 (hU hl).1
    have x2 := xor_enc x1.1 ih.1
    have ex : ∀ X Y : Array Nat, xorRows X Y = xorRows112 X Y := fun _ _ => rfl
    rw [List.map_cons, certSum, ex, ex]
    refine ⟨x2.1, ?_⟩
    rw [x2.2, x1.2, m.2, (hM hl).2, (hU hl).2, ih.2]
    rfl

theorem facts : (Bounded (wordCols a276Word) ∧ powCols (wordCols a276Word) 11 = idRows 11 ∧
      app11 (wordCols a276Word) 14 = 14 ∧
      ∀ n < 2048, app11 (wordCols a276Word) n = n → n = 0 ∨ n = 14)
    ∧ (wSet.length = 16 ∧ wSet.Nodup ∧ (∀ a ∈ wSet, a < 2048) ∧
      ∀ a ∈ wSet, ∀ b ∈ wSet, a ^^^ b ∈ wSet)
    ∧ ((∀ m < 9, 1 ≤ m → Bounded (sCols m) ∧ app11 (sCols m) 1 = 1) ∧
      ∀ p ∈ wPaths, (∀ w ∈ p.2, ∀ m ∈ w, 1 ≤ m ∧ m < 9) ∧ spanOK (pathVecs p) = true)
    ∧ (mulRows 112 (certSum certList) tInvRows = idRows 112 ∧
      (∀ r < 112, ∀ j < 110, (eRows[r]?.getD 0).testBit j = false) ∧
      (rootBits = tInvRows[110]! ∨ rootBits = tInvRows[111]! ∨
        rootBits = tInvRows[110]! ^^^ tInvRows[111]!) ∧
      (∀ p ∈ commPairs, p.1 < 2048 ∧ p.2 < 4) ∧ rootBits ≠ 0 ∧ rootBits < 2 ^ 112 ∧
      (∀ i < 112, tInvRows[i]! < 2 ^ 112) ∧ commPairs.length = 10)
    ∧ (∀ i < 4, app11 generatorColumns[i]! 1 = 1) := by
  have hT := pack_enc ti
  refine ⟨⟨?_, ?_, ?_, fun n hn h => ?_⟩, wset, ⟨fun m hm h1 => ?_, fun p hp => ?_⟩,
    ⟨?_, fun r hr j hj => ?_, misc.1, misc.2.1, misc.2.2.1, misc.2.2.2.1, hT.1.2, misc.2.2.2.2⟩,
    fun i hi => ?_⟩
  · rw [J4XY.wordCols_eq']
    exact CFSG.KS.SporSch.C11.unpack11_bounded _
  · rw [J4XY.wordCols_eq', CFSG.KS.SporSch.C11.powKF_eq 32 _ 11 (by norm_num),
      CFSG.KS.SporSch.C11.id_eq]
    exact congrArg _ (Nat.eq_of_beq_eq_true a1)
  · rw [J4XY.wordCols_eq', CFSG.KS.SporSch.C11.app_eq]
    exact Nat.eq_of_beq_eq_true a2
  · rw [J4XY.wordCols_eq', CFSG.KS.SporSch.C11.app_eq] at h
    have k := allN_spec a3 n hn
    rw [show Nat.beq (CFSG.KS.SporSch.C11.appK (J4XY.W a276Word) n) n = true by rw [h]; exact Nat.beq_refl n] at k
    by_cases h0 : n = 0
    · exact Or.inl h0
    · rw [show Nat.beq n 0 = false from Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)] at k
      exact Or.inr (Nat.eq_of_beq_eq_true k)
  · rw [sc_eq h1 hm, CFSG.KS.SporSch.C11.app_eq]
    exact ⟨CFSG.KS.SporSch.C11.unpack11_bounded _,
      Nat.eq_of_beq_eq_true (allN_spec J4Orbits.fx1 (m - 1) (by omega))⟩
  · have hl := pathLetters p hp
    refine ⟨hl, ?_⟩
    rw [pathVecs_eq p hl]
    exact spanOK_of (CFSG.KS.SporSch.C11.span_sound
      (allL_mem (f := fun p => CFSG.KS.SporSch.C11.spanK (pvK p)) spans p hp))
  · have hc := certSum_ok [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] (by decide)
    have e : certList = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map
        fun l => ((etaP (commM commPairs[l]!)).2, CFSG.Sporadic.J4Schreier.selRows l) := rfl
    rw [e]
    have m := mulRows_enc J4Real.hK hc.1 hT.1
    apply enc_inj m.1 (CFSG.KS.SporSch.J4B.id_enc J4Real.hK).1
    rw [m.2, hc.2, Nat.eq_of_beq_eq_true cs, hT.2, (CFSG.KS.SporSch.J4B.id_enc J4Real.hK).2]
    exact Nat.eq_of_beq_eq_true fin
  · simp only [eRows, unitCols, Array.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some,
      -Nat.reducePow]
    have t0 : (0 : Nat).testBit j = false := Nat.zero_testBit j
    have t1 : (2 ^ 110 : Nat).testBit j = false := by
      rw [Nat.testBit_two_pow]
      exact decide_eq_false (by omega)
    have t2 : (2 ^ 111 : Nat).testBit j = false := by
      rw [Nat.testBit_two_pow]
      exact decide_eq_false (by omega)
    have u1 : (if r = 0 then 2 ^ 110 else 0 : Nat).testBit j = false := by
      split_ifs
      · exact t1
      · exact t0
    have u2 : (if r = 1 then 2 ^ 111 else 0 : Nat).testBit j = false := by
      split_ifs
      · exact t2
      · exact t0
    rw [Nat.testBit_or]
    exact Bool.or_eq_false_iff.2 ⟨u1, u2⟩
  · rw [J4Five.GC_eq hi, CFSG.KS.SporSch.C11.app_eq]
    exact Nat.eq_of_beq_eq_true (allN_spec gfix i hi)

end CertificateChecks.KernelSporSch.J4Odd

end
