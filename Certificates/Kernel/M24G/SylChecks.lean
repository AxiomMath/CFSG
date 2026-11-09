module

public import Certificates.Data.Kernel.M24G.Syl
public import Certificates.Kernel.M24G.SylData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.ReplayChunk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.SylC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem s0Fix_ok : sylS0FixOn Native.s0Tabs = true := by
  decide +kernel

noncomputable def tripleChunkQ (f a b a' b' : Nat) : Bool :=
  ReplayQ.chunkB Native.keyTriple sylTripleSteps (posTreeB Native.keyTriple SylD.tL) SylD.tL
    SylD.tPar SylD.tGen f a b a' b'

set_option maxHeartbeats 0 in
theorem tripleChunk1 : tripleChunkQ 256 0 1 256 559 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem tripleChunk2 : tripleChunkQ 256 256 559 512 852 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem tripleChunk3 : tripleChunkQ 256 512 852 768 981 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem tripleChunk4 : tripleChunkQ 256 768 981 1024 1024 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem tripleGoEnd : replayGoB Native.keyTriple sylTripleSteps
    (posTreeB Native.keyTriple SylD.tL) 76 (SylD.tL.drop 1024) 1024 (SylD.tL.drop 1024)
    (SylD.tPar.drop 1024) (SylD.tGen.drop 1024) 1024 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem triplePos1 : ReplayQ.posAllN Native.keyTriple (posTreeB Native.keyTriple SylD.tL) 512
    (SylD.tL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem triplePosEnd : posAllB Native.keyTriple (posTreeB Native.keyTriple SylD.tL)
    (SylD.tL.drop 512) 512 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem tripleSize_ok :
    (sizeK (posTreeB Native.keyTriple SylD.tL) == SylD.tL.length) = true := by
  quickRfl

theorem tripleHead_ok : ReplayQ.headB (0, 8, 16) SylD.tL SylD.tPar SylD.tGen = true := by
  quickRfl

theorem triple_ok : replayOK Native.keyTriple sylTripleSteps (0, 8, 16) 1100 SylD.tL SylD.tPar
    SylD.tGen (posTree Native.keyTriple SylD.tL) = true := by
  rw [replayOK_eq_B, posTree_eq_B]
  refine ReplayQ.replayOKB_of tripleSize_ok ?_ tripleHead_ok ?_
  · exact ReplayQ.posAllB_chunk triplePos1 triplePosEnd
  · exact (ReplayQ.replayGoB_chunk tripleChunk1 844).trans
      ((ReplayQ.replayGoB_chunk tripleChunk2 588).trans
      ((ReplayQ.replayGoB_chunk tripleChunk3 332).trans
      ((ReplayQ.replayGoB_chunk tripleChunk4 76).trans tripleGoEnd)))

theorem tripleLen_ok : SylD.tL.length = 1024 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tripleValid_ok : SylD.tL.all Native.validTriple = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tuple_ok : replayOK Native.keyOSP sylOSPSteps Native.tup0 200 SylD.uL SylD.uPar SylD.uGen
    (posTree Native.keyOSP SylD.uL) = true := by
  decide +kernel

theorem tupleLen_ok : SylD.uL.length = 63 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tupleValid_ok : SylD.uL.all Native.validOSP = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem fixed_ok : sylFixedOn sylS0BT = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls_ok : sylClsF SL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem trioDet_ok : sylTrioDetF TS = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem v0_ok : sylV0F SL TS = true := by
  decide +kernel

@[expose] def bitQ (M x : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight M x) 1) 1

theorem bitQ_eq (M x : Nat) : bitQ M x = M.testBit x := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((M >>> x) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  by_cases h : M / 2 ^ x % 2 = 1
  · rw [h, decide_eq_true rfl]
    exact Nat.beq_refl 1
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)

theorem beqQ (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [beq_self_eq_true, Nat.beq_refl]
  · rw [beq_eq_false_iff_ne.mpr h]
    exact (Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)).symm

theorem bneQ (a b : Nat) : (a != b) = !Nat.beq a b := by
  rw [bne, beqQ]

theorem listBeq_eqQ (l m : List Nat) : (l == m) = ReplayQ.listBeqQ l m := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ReplayQ.listBeqQ_iff]

@[expose] def memQ (x : Nat) : List Nat → Bool
  | [] => false
  | a :: l => Nat.beq x a || memQ x l

theorem contains_eq_memQ (x : Nat) : ∀ l : List Nat, l.contains x = memQ x l
  | [] => rfl
  | a :: l => by rw [List.contains_cons, memQ, beqQ, contains_eq_memQ x l]

@[expose] def insQ (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => bif Nat.ble a b then a :: b :: l else b :: insQ a l

@[expose] def sortQ : List Nat → List Nat
  | [] => []
  | b :: l => insQ b (sortQ l)

theorem insN_eq_Q (a : Nat) : ∀ l, insN a l = insQ a l
  | [] => rfl
  | b :: l => by
    by_cases h : a ≤ b
    · have hb : Nat.ble a b = true := Nat.ble_eq.mpr h
      simp only [insN, insQ, h, hb, Bool.cond_true, ↓reduceIte]
    · have hb : Nat.ble a b = false := Bool.eq_false_iff.mpr fun e => h (Nat.ble_eq.mp e)
      simp only [insN, insQ, h, hb, Bool.cond_false, ↓reduceIte, insN_eq_Q a l]

theorem sortN_eq_Q : ∀ l, sortN l = sortQ l
  | [] => rfl
  | b :: l => by rw [sortN, sortQ, sortN_eq_Q l, insN_eq_Q]

@[expose] def candQ (K v w : Nat) : Bool :=
  bitQ K v && bitQ K (31 ^^^ v) && !Nat.beq v 0 && !Nat.beq v 31 && !Nat.beq w 0 &&
    !Nat.beq w 31 && !Nat.beq w v && !Nat.beq w (31 ^^^ v) && bitQ K w && bitQ K (31 ^^^ w) &&
    bitQ K (v ^^^ w) && bitQ K (31 ^^^ v ^^^ w)

@[expose] def actMQ : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, m =>
    Nat.xor (bif Nat.beq (Nat.land m 1) 1 then c else 0) (actMQ cs (Nat.shiftRight m 1))

theorem actM_eq_Q : ∀ (cs : List Nat) (m : Nat), Native.actM cs m = actMQ cs m
  | [], _ => rfl
  | c :: cs, m => by
    have h1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    have h2 : Nat.shiftRight m 1 = m / 2 :=
      (Nat.shiftRight_eq_div_pow m 1).trans (by rw [Nat.pow_one])
    rw [Native.actM, actMQ, actM_eq_Q cs, h1, h2]
    by_cases h : m % 2 = 1
    · simp only [h, ↓reduceIte]
      rfl
    · have hb : Nat.beq (m % 2) 1 = false :=
        Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)
      simp only [h, hb, Bool.cond_false, ↓reduceIte]
      rfl

@[expose] def imgQ (bt : Nat × Nat × Nat) (m : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.mod (Nat.shiftRight bt.1 (Nat.mul 24 (Nat.mod m 256))) 16777216)
    (Nat.mod (Nat.shiftRight bt.2.1 (Nat.mul 24 (Nat.mod (Nat.shiftRight m 8) 256))) 16777216))
    (Nat.mod (Nat.shiftRight bt.2.2 (Nat.mul 24 (Nat.mod (Nat.shiftRight m 16) 256))) 16777216)

@[expose] def toddQ (bt : Nat × Nat × Nat) (m : Nat) : Nat :=
  actMQ Native.ccEColsN (imgQ bt (actMQ Native.liftEColsN m))

theorem toddActF_eq_Q : toddActF = toddQ := by
  funext bt m
  rw [toddActF, toddQ, actM_eq_Q, actM_eq_Q]
  rfl

theorem actMQ_append : ∀ (cs1 cs2 : List Nat) (m : Nat),
    actMQ (cs1 ++ cs2) m = Nat.xor (actMQ cs1 m) (actMQ cs2 (Nat.shiftRight m cs1.length))
  | [], _, _ => (Nat.zero_xor _).symm
  | c :: cs1, cs2, m => by
    rw [List.cons_append, actMQ, actMQ, actMQ_append cs1 cs2, List.length_cons]
    change _ = Nat.xor (Nat.xor _ _) (actMQ cs2 (m >>> (cs1.length + 1)))
    rw [Nat.add_comm cs1.length 1, Nat.shiftRight_add]
    exact (Nat.xor_assoc _ _ _).symm

theorem actMQ_low : ∀ (cs : List Nat) (m : Nat), actMQ cs m = actMQ cs (m % 2 ^ cs.length)
  | [], _ => rfl
  | c :: cs, m => by
    have e1 : Nat.land (m % 2 ^ (cs.length + 1)) 1 = Nat.land m 1 := by
      change (m % 2 ^ (cs.length + 1)) &&& 1 = m &&& 1
      rw [Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.pow_succ, Nat.mod_mul_left_mod]
    have e2 :
        Nat.shiftRight (m % 2 ^ (cs.length + 1)) 1 = (Nat.shiftRight m 1) % 2 ^ cs.length := by
      change (m % 2 ^ (cs.length + 1)) >>> 1 = (m >>> 1) % 2 ^ cs.length
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.pow_succ',
        Nat.mod_mul_right_div_self]
    rw [List.length_cons, actMQ, actMQ, e1, e2, ← actMQ_low cs]

@[expose] def tabQ (T w b : Nat) : Nat := Nat.mod (Nat.shiftRight T (Nat.mul w b)) (Nat.pow 2 w)

@[expose] def packW (w : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => Nat.add x (Nat.mul (Nat.pow 2 w) (packW w l))

theorem actMQ_tab {cs : List Nat} {T w : Nat} (hl : cs.length = 8)
    (hT : Native.allLt 256 (fun b => Nat.beq (tabQ T w b) (actMQ cs b)) = true) (m : Nat) :
    actMQ cs m = tabQ T w (Nat.mod m 256) := by
  have hb := List.all_eq_true.1 hT (m % 256) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  rw [actMQ_low, hl]
  exact (Nat.eq_of_beq_eq_true hb).symm

@[expose] def ccT0 : Nat := packW 11 ((List.range 256).map (actMQ (Native.ccEColsN.take 8)))

@[expose] def ccT1 : Nat :=
  packW 11 ((List.range 256).map (actMQ ((Native.ccEColsN.drop 8).take 8)))

@[expose] def ccT2 : Nat := packW 11 ((List.range 256).map (actMQ (Native.ccEColsN.drop 16)))

@[expose] def liftT0 : Nat := packW 24 ((List.range 256).map (actMQ (Native.liftEColsN.take 8)))

theorem ccT0_ok :
    Native.allLt 256 (fun b => Nat.beq (tabQ ccT0 11 b) (actMQ (Native.ccEColsN.take 8) b)) =
      true := by
  quickRfl

theorem ccT1_ok : Native.allLt 256 (fun b =>
    Nat.beq (tabQ ccT1 11 b) (actMQ ((Native.ccEColsN.drop 8).take 8) b)) = true := by
  quickRfl

theorem ccT2_ok :
    Native.allLt 256 (fun b => Nat.beq (tabQ ccT2 11 b) (actMQ (Native.ccEColsN.drop 16) b)) =
      true := by
  quickRfl

theorem liftT0_ok :
    Native.allLt 256 (fun b => Nat.beq (tabQ liftT0 24 b) (actMQ (Native.liftEColsN.take 8) b)) =
      true := by
  quickRfl

@[expose] def ccQ (x : Nat) : Nat :=
  Nat.xor (tabQ ccT0 11 (Nat.mod x 256)) (Nat.xor (tabQ ccT1 11 (Nat.mod (Nat.shiftRight x 8) 256))
    (tabQ ccT2 11 (Nat.mod (Nat.shiftRight (Nat.shiftRight x 8) 8) 256)))

@[expose] def liftQ (m : Nat) : Nat :=
  Nat.xor (tabQ liftT0 24 (Nat.mod m 256)) (actMQ (Native.liftEColsN.drop 8) (Nat.shiftRight m 8))

@[expose] def toddT (bt : Nat × Nat × Nat) (m : Nat) : Nat := ccQ (imgQ bt (liftQ m))

theorem toddQ_eq_T : toddQ = toddT := by
  have ec : Native.ccEColsN = Native.ccEColsN.take 8 ++
      ((Native.ccEColsN.drop 8).take 8 ++ Native.ccEColsN.drop 16) := rfl
  have el : Native.liftEColsN = Native.liftEColsN.take 8 ++ Native.liftEColsN.drop 8 := rfl
  have hc : ∀ x, actMQ Native.ccEColsN x = ccQ x := fun x => by
    rw [ec, actMQ_append, actMQ_append, actMQ_tab rfl ccT0_ok, actMQ_tab rfl ccT1_ok,
      actMQ_tab rfl ccT2_ok]
    rfl
  have hl : ∀ m, actMQ Native.liftEColsN m = liftQ m := fun m => by
    rw [el, actMQ_append, actMQ_tab rfl liftT0_ok]
    rfl
  funext bt m
  rw [toddQ, toddT, hl, hc]

@[expose] def invQ (v w : Nat) : Bool :=
  sylS0BT.all fun bt =>
    memQ (toddT bt v) (Native.sp8 v w) && memQ (toddT bt w) (Native.sp8 v w)

@[expose] def rowQ (K v w : Nat) : Bool :=
  !(candQ K v w) || !(invQ v w) || ReplayQ.listBeqQ (sortQ (Native.sp8 v w)) Native.v0List ||
    ReplayQ.listBeqQ (sortQ (Native.sp8 v w)) Native.vpList

@[expose] def moveQ (v : Nat) : Option Nat :=
  (sylS0BT.map fun bt => toddT bt v).find? fun u =>
    !(Nat.beq u 0 || Nat.beq u 31 || Nat.beq u v || Nat.beq u (31 ^^^ v))

@[expose] def spanVQ (K v : Nat) : Bool :=
  !(bitQ K v && bitQ K (31 ^^^ v) && !Nat.beq v 0 && !Nat.beq v 31) ||
    match moveQ v with
    | some u => [u, u ^^^ 31, u ^^^ v, u ^^^ 31 ^^^ v].all (rowQ K v)
    | none => Native.allLt 2048 (rowQ K v)

theorem sylRow_eq_Q : sylRow = rowQ := by
  funext K v w
  simp only [sylRow, rowQ, sylCand, candQ, sylInv, invQ, bitQ_eq, bneQ, contains_eq_memQ,
    sortN_eq_Q, listBeq_eqQ, toddActF_eq_Q, toddQ_eq_T]

theorem sylSpanOn_eq_Q : sylSpanOn = fun K => Native.allLt 2048 (spanVQ K) := by
  have hm : sylMove = moveQ := by
    funext v
    simp only [sylMove, moveQ, beqQ, toddActF_eq_Q, toddQ_eq_T]
  funext K
  unfold sylSpanOn
  congr 1
  funext v
  simp only [sylSpanV, spanVQ, hm, sylRow_eq_Q, bitQ_eq, bneQ]
  rfl

set_option maxHeartbeats 0 in
theorem span_ok : sylSpanOn (sylClsMask SL) = true := by
  rw [sylSpanOn_eq_Q]
  quickRfl

@[expose] def spStepsQ : List (List Nat → List Nat) :=
  Native.genTabs.map fun g L => sortQ (L.map (toddT (imgTab g.toList)))

theorem sylSpSteps_eq_Q : sylSpSteps = spStepsQ := by
  unfold sylSpSteps spStepsQ
  congr 1
  funext g L
  rw [sylSpF, sortN_eq_Q, toddActF_eq_Q, toddQ_eq_T]

noncomputable def spaceChunkQ (f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB _ ReplayQ.decEqLQ Native.keySp spStepsQ (posTreeB Native.keySp SylD.vL) SylD.vL
    SylD.vPar SylD.vGen f a b a' b'

set_option maxHeartbeats 0 in
theorem spaceChunk1 : spaceChunkQ 800 0 1 800 1092 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem spaceChunk2 : spaceChunkQ 800 800 1092 1600 2158 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem spaceChunk3 : spaceChunkQ 800 1600 2158 2400 3108 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem spaceChunk4 : spaceChunkQ 528 2400 3108 2928 3796 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem spaceGoEnd : @replayGoB _ ReplayQ.decEqLQ Native.keySp spStepsQ
    (posTreeB Native.keySp SylD.vL) 0 (SylD.vL.drop 2928) 2928 (SylD.vL.drop 3796)
    (SylD.vPar.drop 3796) (SylD.vGen.drop 3796) 3796 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem spacePos1 : ReplayQ.posAllN Native.keySp (posTreeB Native.keySp SylD.vL) 1000
    (SylD.vL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem spacePos2 : ReplayQ.posAllN Native.keySp (posTreeB Native.keySp SylD.vL) 1000
    (SylD.vL.drop 1000) 1000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem spacePos3 : ReplayQ.posAllN Native.keySp (posTreeB Native.keySp SylD.vL) 1000
    (SylD.vL.drop 2000) 2000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem spacePosEnd : posAllB Native.keySp (posTreeB Native.keySp SylD.vL)
    (SylD.vL.drop 3000) 3000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem spaceSize_ok : (sizeK (posTreeB Native.keySp SylD.vL) == SylD.vL.length) = true := by
  quickRfl

theorem spaceHead_ok :
    @ReplayQ.headB _ ReplayQ.decEqLQ Native.vpList SylD.vL SylD.vPar SylD.vGen = true := by
  quickRfl

theorem space_ok : replayOK Native.keySp sylSpSteps Native.vpList 2928 SylD.vL SylD.vPar SylD.vGen
    (posTree Native.keySp SylD.vL) = true := by
  rw [replayOK_eq_B, posTree_eq_B, ReplayQ.replayOKB_inst _ ReplayQ.decEqLQ, sylSpSteps_eq_Q]
  refine @ReplayQ.replayOKB_of _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ spaceSize_ok ?_ spaceHead_ok ?_
  · exact ReplayQ.posAllB_chunk spacePos1 (ReplayQ.posAllB_chunk spacePos2
      (ReplayQ.posAllB_chunk spacePos3 spacePosEnd))
  · exact (@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ spaceChunk1 2128).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ spaceChunk2 1328).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ spaceChunk3 528).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ spaceChunk4 0).trans
        spaceGoEnd)))

theorem spaceLen_ok : SylD.vL.length = 3796 := by
  decide +kernel

theorem testBit_orMaskS (m : Nat) : ∀ l : List Nat, (orMask l).testBit m = l.contains m
  | [] => by simp [orMask]
  | c :: l => by
    rw [orMask, Nat.testBit_or, testBit_orMaskS m l, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.contains_cons]
    by_cases hc : c = m
    · subst hc
      simp
    · simp [hc, Ne.symm hc]

@[expose] def ltChainQ : List Nat → Bool
  | a :: b :: l => Nat.blt a b && ltChainQ (b :: l)
  | _ => true

theorem pairwise_of_ltChainQ : ∀ L : List Nat, ltChainQ L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ltChainQ, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := pairwise_of_ltChainQ (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

@[expose] def span3 (a b c : Nat) : List Nat :=
  [0, a, b, a ^^^ b, c, a ^^^ c, b ^^^ c, a ^^^ b ^^^ c]

theorem xor_left_commS (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem xor_cancel_leftS (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem span3_closed {a b c x y : Nat} (hx : x ∈ span3 a b c) (hy : y ∈ span3 a b c) :
    x ^^^ y ∈ span3 a b c := by
  simp only [span3, List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.xor_comm, xor_left_commS, xor_cancel_leftS, Nat.xor_self, Nat.xor_zero,
      true_or, or_true]

@[expose] def closedM (M : Nat) : List Nat → Bool
  | _ :: a :: b :: c :: d :: _ =>
    Nat.beq M (orMask (span3 a b c)) || Nat.beq M (orMask (span3 a b d))
  | _ => false

theorem closedXor_of_M {L : List Nat} (h : closedM (orMask L) L = true) :
    Native.closedXor L = true := by
  obtain ⟨a, b, c, hc⟩ : ∃ a b c, orMask L = orMask (span3 a b c) := by
    match L, h with
    | _ :: a :: b :: c :: d :: _, h =>
      simp only [closedM, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨a, b, c, Nat.eq_of_beq_eq_true h⟩
      · exact ⟨a, b, d, Nat.eq_of_beq_eq_true h⟩
    | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h => simp [closedM] at h
  have hm : ∀ x, x ∈ L ↔ x ∈ span3 a b c := fun x => by
    rw [← List.contains_iff_mem, ← List.contains_iff_mem, ← testBit_orMaskS, ← testBit_orMaskS,
      hc]
  unfold Native.closedXor
  simp only [List.all_eq_true, List.contains_iff_mem, hm]
  intro x hx y hy
  exact span3_closed hx hy

@[expose] def validSpM (M : Nat) (L : List Nat) : Bool :=
  L.all (fun m => Nat.blt m 2048) && ltChainQ L && closedM M L && bitQ M 0

theorem validSp_of_M {L : List Nat} (h : validSpM (orMask L) L = true) :
    Native.validSp L = true := by
  simp only [validSpM, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, bitQ_eq,
    testBit_orMaskS] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [Native.validSp, closedXor_of_M h3, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, and_true]
  exact ⟨⟨h1, pairwise_of_ltChainQ L h2⟩, h4⟩

set_option maxHeartbeats 0 in
theorem spaceValidM_ok : SylD.vL.all (fun L => validSpM (orMask L) L) = true := by
  quickRfl

theorem spaceValid_ok : SylD.vL.all Native.validSp = true :=
  List.all_eq_true.2 fun L hL => validSp_of_M (List.all_eq_true.1 spaceValidM_ok L hL)

end CFSG.KC.M24G.SylC
