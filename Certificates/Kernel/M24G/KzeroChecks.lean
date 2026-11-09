module

public import Certificates.Data.Kernel.M24G.Kzero
public import Certificates.Kernel.M24G.KzeroData
public import Certificates.Kernel.M24G.FixOctFast
public import Certificates.Kernel.M24G.ReplayChunk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.KzeroC

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

@[expose] def keyQ5 : List Nat → Nat → Nat
  | [], acc => acc
  | m :: l, acc => keyQ5 l (Nat.lor (Nat.shiftLeft acc 5) m)

@[expose] def kzeroKeyQ (t : Array Nat) : Nat :=
  bif Nat.beq t.size 24 then keyQ5 t.toList 0 else Native.kzeroKey t

theorem foldl_eq_keyQ5 : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc x => (acc <<< 5) ||| x) acc = keyQ5 l acc
  | [], _ => rfl
  | _ :: l, _ => foldl_eq_keyQ5 l _

theorem kzeroKeyF_eq_Q : kzeroKeyF = kzeroKeyQ := by
  funext t
  unfold kzeroKeyF kzeroKeyQ
  by_cases h : t.size = 24
  · have hb : Nat.beq t.size 24 = true := by rw [h]; rfl
    rw [ite_eq_left h, hb]
    exact foldl_eq_keyQ5 t.toList 0
  · have hb : Nat.beq t.size 24 = false :=
      Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)
    rw [ite_eq_right h, hb]
    rfl

@[expose] def kzC0 : Nat := 467609085860506254666317780031894624405236386801781965056

@[expose] def kzC1 : Nat := 492418238363641336356315449103051971147493076074649486596

@[expose] def kzC2 : Nat := 393954270145167749522519027333817996947414276066918204676

@[expose] def kzC3 : Nat := 197025588250683647149021782177244209051130261206550906116

@[expose] def kzeroStepsQ : List (Array Nat → Array Nat) :=
  [FixOctQ.mulPF kzC0 (Native.s0Tabs.getD 0 #[]), FixOctQ.mulPF kzC1 (Native.s0Tabs.getD 1 #[]),
    FixOctQ.mulPF kzC2 (Native.s0Tabs.getD 2 #[]), FixOctQ.mulPF kzC3 (Native.s0Tabs.getD 3 #[])]

theorem kzeroStepsF_eq_P : kzeroStepsF = kzeroStepsQ := by
  have e : kzeroStepsF = [mulTabF (Native.s0Tabs.getD 0 #[]), mulTabF (Native.s0Tabs.getD 1 #[]),
      mulTabF (Native.s0Tabs.getD 2 #[]), mulTabF (Native.s0Tabs.getD 3 #[])] := rfl
  rw [e, FixOctQ.mulTabF_eq_P (C := kzC0) (c := Native.s0Tabs.getD 0 #[])
      (FixOctQ.lookP_spec (by decide) (by decide) (by decide)),
    FixOctQ.mulTabF_eq_P (C := kzC1) (c := Native.s0Tabs.getD 1 #[])
      (FixOctQ.lookP_spec (by decide) (by decide) (by decide)),
    FixOctQ.mulTabF_eq_P (C := kzC2) (c := Native.s0Tabs.getD 2 #[])
      (FixOctQ.lookP_spec (by decide) (by decide) (by decide)),
    FixOctQ.mulTabF_eq_P (C := kzC3) (c := Native.s0Tabs.getD 3 #[])
      (FixOctQ.lookP_spec (by decide) (by decide) (by decide))]
  rfl

noncomputable def kzeroChunkQ (f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB _ ReplayQ.decEqQ kzeroKeyQ kzeroStepsQ (posTreeB kzeroKeyQ KzeroD.zL) KzeroD.zL
    KzeroD.zPar KzeroD.zGen f a b a' b'

set_option maxHeartbeats 0 in
theorem kzeroChunk1 : kzeroChunkQ 256 0 1 256 559 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem kzeroChunk2 : kzeroChunkQ 256 256 559 512 852 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem kzeroChunk3 : kzeroChunkQ 256 512 852 768 981 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem kzeroChunk4 : kzeroChunkQ 256 768 981 1024 1024 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem kzeroGoEnd : @replayGoB _ ReplayQ.decEqQ kzeroKeyQ kzeroStepsQ (posTreeB kzeroKeyQ KzeroD.zL)
    76 (KzeroD.zL.drop 1024) 1024 (KzeroD.zL.drop 1024) (KzeroD.zPar.drop 1024)
    (KzeroD.zGen.drop 1024) 1024 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kzeroPos1 :
    ReplayQ.posAllN kzeroKeyQ (posTreeB kzeroKeyQ KzeroD.zL) 512 (KzeroD.zL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kzeroPosEnd :
    posAllB kzeroKeyQ (posTreeB kzeroKeyQ KzeroD.zL) (KzeroD.zL.drop 512) 512 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem kzeroSize_ok : (sizeK (posTreeB kzeroKeyQ KzeroD.zL) == KzeroD.zL.length) = true := by
  quickRfl

theorem kzeroHead_ok :
    @ReplayQ.headB _ ReplayQ.decEqQ Native.kzeroId KzeroD.zL KzeroD.zPar KzeroD.zGen = true := by
  quickRfl

theorem kzeroSyl_ok : replayOK kzeroKeyF kzeroStepsF Native.kzeroId 1100 KzeroD.zL KzeroD.zPar
    KzeroD.zGen (posTree kzeroKeyF KzeroD.zL) = true := by
  rw [replayOK_eq_B, posTree_eq_B, ReplayQ.replayOKB_inst _ ReplayQ.decEqQ, kzeroKeyF_eq_Q,
    kzeroStepsF_eq_P]
  refine @ReplayQ.replayOKB_of _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ kzeroSize_ok ?_ kzeroHead_ok ?_
  · exact ReplayQ.posAllB_chunk kzeroPos1 kzeroPosEnd
  · exact (@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ kzeroChunk1 844).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ kzeroChunk2 588).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ kzeroChunk3 332).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ kzeroChunk4 76).trans
        kzeroGoEnd)))

@[expose] def kzU : Nat := 344528665447885322691125242991403803728226108096770348311

theorem kzeroK0_eq (pos : KTree (Nat × Nat)) (L : List (Array Nat)) :
    kzeroK0F pos L kzeroPairF = L.filter fun t => (findKB (kzeroKeyQ (FixOctQ.mulPF kzU
      (Native.kzeroUInv.headD #[]) (mulTabF t (Native.uTabs.headD #[])))) pos).isSome := by
  simp only [kzeroK0F, kzeroConjF, kzeroPairF, findK_eq_B]
  rw [kzeroKeyF_eq_Q, FixOctQ.mulTabF_eq_P (C := kzU) (c := Native.kzeroUInv.headD #[])
    (FixOctQ.lookP_spec (by decide) (by decide) (by decide))]

@[expose] def small8 : List Nat → Bool
  | [] => true
  | x :: l => Nat.blt x 256 && small8 l

@[expose] def packQ : List Nat → Nat
  | [] => 0
  | x :: l => x + 256 * packQ l

@[expose] def lkQ (P j : Nat) : Nat := Nat.mod (Nat.div P (Nat.pow 256 j)) 256

theorem lkQ_packQ : ∀ l : List Nat, small8 l = true → ∀ j, lkQ (packQ l) j = l.getD j 0
  | [], _, j => by
    change 0 / 256 ^ j % 256 = 0
    rw [Nat.zero_div, Nat.zero_mod]
  | x :: l, h, 0 => by
    simp only [small8, Bool.and_eq_true, Nat.blt_eq] at h
    change (x + 256 * packQ l) / 256 ^ 0 % 256 = x
    rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.1]
  | x :: l, h, j + 1 => by
    simp only [small8, Bool.and_eq_true, Nat.blt_eq] at h
    change (x + 256 * packQ l) / 256 ^ (j + 1) % 256 = l.getD j 0
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide),
      Nat.div_eq_of_lt h.1, Nat.zero_add]
    exact lkQ_packQ l h.2 j

@[expose] def kzUL : List Nat :=
  [18, 16, 19, 17, 15, 14, 12, 13, 4, 5, 7, 6, 21, 22, 23, 20, 8, 11, 10, 9, 3, 1, 2, 0]

@[expose] def mulUQ (t : Array Nat) : Array Nat :=
  bif small8 t.toList then (kzUL.map (lkQ (packQ t.toList))).toArray
  else mulTabF t (Native.uTabs.headD #[])

theorem mulTabF_u_eq (t : Array Nat) : mulTabF t (Native.uTabs.headD #[]) = mulUQ t := by
  unfold mulUQ
  cases h : small8 t.toList
  · rfl
  · have hu : (List.range 24).map (fun i => (Native.uTabs.headD #[]).toList.getD i 0) = kzUL := by
      decide
    rw [Bool.cond_true, mulTabF, ← hu, List.map_map]
    congr 1
    exact List.map_congr_left fun j _ => (lkQ_packQ _ h _).symm

set_option maxHeartbeats 0 in
theorem kzeroK0_ok : kzeroK0F (posTree kzeroKeyF KzeroD.zL) KzeroD.zL kzeroPairF = KzeroD.kL := by
  rw [kzeroK0_eq, posTree_eq_B, kzeroKeyF_eq_Q]
  simp only [mulTabF_u_eq]
  decide +kernel

theorem kzeroKLen_ok : KzeroD.kL.length = 64 := by
  decide +kernel

end CFSG.KC.M24G.KzeroC
