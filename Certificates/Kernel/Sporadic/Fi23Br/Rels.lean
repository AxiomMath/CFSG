
module

public import CFSG.Sporadic.Fi23.SimpleBase
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Presentation.Fi23
public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.Sporadic.RelSeg
public import Certificates.Kernel.Sporadic.Fi23Br.Data
public import Certificates.Kernel.Sporadic.Fi23Br.Words
import Certificates.Kernel.Sporadic.Fi23Br.Checks
import Certificates.Kernel.Sporadic.Fi23Br.Seed
import Certificates.Kernel.Sporadic.Fi23Br.R0
import Certificates.Kernel.Sporadic.Fi23Br.R1
import Certificates.Kernel.Sporadic.Fi23Br.R2
import Certificates.Kernel.Sporadic.Fi23Br.R3
import Certificates.Kernel.Sporadic.Fi23Br.R4
import Certificates.Kernel.Sporadic.Fi23Br.R5
import Certificates.Kernel.Sporadic.Fi23Br.R6
import Certificates.Kernel.Sporadic.Fi23Br.R7
import Certificates.Kernel.Sporadic.Fi23Br.R8
import Certificates.Kernel.Sporadic.Fi23Br.R9
import CFSG.Certificates.Kernel.Spor.BytesFSound
import CFSG.Certificates.Kernel.CosetJ.WordsTSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.ForallChunks
import Certificates.Kernel.Sporadic.BrChain
import Certificates.Kernel.Sporadic.OrdCommon
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.F3.SepSpec
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Fi23.CertificateBase
public import CFSG.Sporadic.Fi23.SlpSpec
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import Certificates.Kernel.Sporadic.Fi23Br.RelC

public section

set_option maxRecDepth 400000

namespace CFSG.KD.BrFi23

#kc_forall_chunks RC.all (fun r => relC r = true) 55 CFSG.KD.BrFi23.relC 1

end CFSG.KD.BrFi23

namespace CertificateChecks.KernelSpor.Fi23Rels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.RelSeg CFSG.KD.BrFi23
open CFSG.Sporadic.Bridge.Fi23GPL.Native

noncomputable abbrev Mt (Y : Nat) : Matrix (Fin 253) (Fin 253) (ZMod 3) := ordMat 3 253 11 2783 Y

noncomputable abbrev M (g : Nat) : Matrix (Fin 253) (Fin 253) (ZMod 3) := Mt (RB g)

abbrev SP (r lo hi Sin Sout : Nat) : Prop :=
  SegP (nat_lit 3) (nat_lit 253) (nat_lit 11) (nat_lit 2783) (nat_lit 12) RB relsX r lo hi Sin Sout

theorem seg {r lo hi Sin Sout : Nat}
    (h : relSegOK RB (mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253) (nat_lit 8) L H CM RM)
      relsX ONE (nat_lit 12) r lo hi Sin Sout = true) : SP r lo hi Sin Sout :=
  segP_of_check consts (nb := nat_lit 704099) rfl hroots hinv relB h

theorem full {r : Nat}
    (h : relOK RB (mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253) (nat_lit 8) L H CM RM)
      relsX (nat_lit 12) ONE r = true) : SP r 0 (lenL (nthRel relsX r)) ONE ONE :=
  segP_of_relOK consts (nb := nat_lit 704099) rfl hroots hinv relB h

theorem fin {r n : Nat} (h : SP r 0 n ONE ONE) (e : Nat.beq (lenL (nthRel relsX r)) n = true) :
    SP r 0 (lenL (nthRel relsX r)) ONE ONE := by
  rw [Nat.eq_of_beq_eq_true e]
  exact h

theorem all_segs : ∀ r < lenL relsX, SP r 0 (lenL (nthRel relsX r)) ONE ONE := by
  intro r hr
  have hn := Nat.eq_of_beq_eq_true relN
  rw [show lenL relsX = 69 from hn] at hr
  by_cases h1 : r < 55
  · exact full (RC.all r h1)
  interval_cases r
  · exact fin (segP_join (seg rsC0) (seg rsC1)) (by quickRfl)
  · exact full relC56
  · exact fin (segP_join (seg rsC2) (seg rsC3)) (by quickRfl)
  · exact fin (segP_join (seg rsC4) (seg rsC5)) (by quickRfl)
  · exact fin (segP_join (seg rsC6) (seg rsC7)) (by quickRfl)
  · exact fin (segP_join (seg rsC8) (seg rsC9)) (by quickRfl)
  · exact fin (segP_join (seg rsC10) (seg rsC11)) (by quickRfl)
  · exact fin (segP_join (seg rsC12) (seg rsC13)) (by quickRfl)
  · exact fin (segP_join (seg rsC14) (seg rsC15)) (by quickRfl)
  · exact fin (segP_join (seg rsC16) (seg rsC17)) (by quickRfl)
  · exact fin (segP_join (seg rsC18) (seg rsC19)) (by quickRfl)
  · exact fin (segP_join (seg rsC20) (seg rsC21)) (by quickRfl)
  · exact fin (segP_join (segP_join (segP_join (segP_join (segP_join (segP_join (seg rsC22)
      (seg rsC23)) (seg rsC24)) (seg rsC25)) (seg rsC26)) (seg rsC27)) (seg rsC28)) (by quickRfl)
  · exact fin (segP_join (segP_join (segP_join (segP_join (segP_join (seg rsC29) (seg rsC30))
      (seg rsC31)) (seg rsC32)) (seg rsC33)) (seg rsC34)) (by quickRfl)

theorem rels_one : ∀ v ∈ relsX, (v.map fun x => Mt (letM RB 12 x)).prod = 1 :=
  rels_of_segP consts all_segs

theorem pair : ∀ g < 12, M (g + 1) * M (12 + 1 + g) = 1 :=
  (rels_sound (rels := []) consts rfl hroots hinv rfl
    (fun r hr => absurd hr (Nat.not_lt_zero r))).1

theorem inv_eq {g : Nat} (hg : g < 12) : (M (g + 1))⁻¹ = M (12 + 1 + g) :=
  Matrix.inv_eq_right_inv (pair g hg)

theorem bounded : ∀ v ∈ relsX, ∀ x ∈ v, x.1 < 12 := relsBounded_spec relB

theorem letM_mat {x : Nat × Bool} (hx : x.1 < 12) :
    Mt (letM RB 12 x) = if x.2 then M (x.1 + 1) else (M (x.1 + 1))⁻¹ := by
  obtain ⟨g, s⟩ := x
  cases s
  · rw [inv_eq hx]
    rfl
  · rfl

theorem mul_comm_one {p d : Nat} {A B : Matrix (Fin d) (Fin d) (ZMod p)} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.1 h

theorem word_eq {u : List (Nat × Bool)} {g : Nat} (hg : g < 12) (hu : u ++ [(g, false)] ∈ relsX) :
    (u.map fun x => Mt (letM RB 12 x)).prod = M (g + 1) := by
  have h := rels_one _ hu
  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton] at h
  have hq : M (12 + 1 + g) * M (g + 1) = 1 := mul_comm_one (pair g hg)
  have e : Mt (letM RB 12 (g, false)) = M (12 + 1 + g) := rfl
  rw [e] at h
  calc (u.map fun x => Mt (letM RB 12 x)).prod
      = (u.map fun x => Mt (letM RB 12 x)).prod * (M (12 + 1 + g) * M (g + 1)) := by
        rw [hq, mul_one]
    _ = M (g + 1) := by rw [← mul_assoc, h, one_mul]

theorem seed_sound1 {p d w S T L H CM RM ONE LV HV nb lb len M St : Nat} {F : Nat → Nat}
    {cs : List Char} {Cs : List Nat}
    (hr : Nat.beq (decRun F lb len p d w S RM M Cs (nat_lit 1)) St = true)
    (hd : seedDone d (validM p nb L H) M St = true)
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hb : CFSG.KS.Bytes.bytesEqK cs F lb len = true)
    (hCs : Cs = List.range ((len + lb - 1) / lb)) :
    CFSG.Blueprint.NativeSporadic.decode p d 1 (String.ofList cs) = ordMat p d w S M :=
  seed_sound hc hnb hb hCs hr hd

theorem mA_eq : CFSG.Sporadic.Fi23.mA = M 11 := by
  have hr := BrChain.run_chain_to (run := decRun P1 256 65042 3 253 11 2783 RM (RB 11)) (fun _ => rfl)
      (decRun_append P1 256 65042 3 253 11 2783 RM (RB 11)) dL (fun k => DA1.getD k 0) 16
      (nat_lit 1) (nat_lit 256039) rfl rfl D1.all
  have h := seed_sound1 hr d1_end consts rfl
    (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) seed1_run) (by decide +kernel)
  change CFSG.Blueprint.NativeSporadic.decode 3 253 1 CFSG.Blueprint.NativeSporadic.Fi23Seed1 = _
  rw [← CFSG.Sporadic.Fi23.seedA_eq, Fi23SeedA.eq, h]

theorem mB_eq : CFSG.Sporadic.Fi23.mB = M 12 := by
  have hr := BrChain.run_chain_to (run := decRun P2 256 65042 3 253 11 2783 RM (RB 12)) (fun _ => rfl)
      (decRun_append P2 256 65042 3 253 11 2783 RM (RB 12)) dL (fun k => DA2.getD k 0) 16
      (nat_lit 1) (nat_lit 256039) rfl rfl D2.all
  have h := seed_sound1 hr d2_end consts rfl
    (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) seed2_run) (by decide +kernel)
  change CFSG.Blueprint.NativeSporadic.decode 3 253 1 CFSG.Blueprint.NativeSporadic.Fi23Seed2 = _
  rw [← CFSG.Sporadic.Fi23.seedB_eq, Fi23SeedB.eq, h]

theorem img_eq : imgWords = IT.W.toArray := by
  have h := CFSG.KC.WordsT.wordsT_sound (cs := IT.chars) (L := IT.W) (by quickRfl)
  rw [← IT.eq] at h
  exact h

theorem surj_eq : surjWords = ST.W.toArray := by
  have h := CFSG.KC.WordsT.wordsT_sound (cs := ST.chars) (L := ST.W) (by quickRfl)
  rw [← ST.eq] at h
  exact h

theorem IT_len : IT.W.length = 10 := by decide +kernel

theorem ST_len : ST.W.length = 2 := by decide +kernel

theorem ST_letters : ∀ w ∈ ST.W, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10 := by decide +kernel

theorem img_mem {k : Nat} (hk : k < 10) :
    (IT.W[k]'(by rw [IT_len]; exact hk)).map seedL ++ [(k, false)] ∈ relsX := by
  unfold relsX
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_map]
  exact ⟨(IT.W[k]'(by rw [IT_len]; exact hk), k), List.mem_zipIdx_iff_getElem?.2 (by simp), rfl⟩

theorem surj_mem {i : Nat} (hi : i < 2) :
    (ST.W[i]'(by rw [ST_len]; exact hi)).map imgL ++ [(10 + i, false)] ∈ relsX := by
  unfold relsX
  apply List.mem_append_right
  rw [List.mem_map]
  exact ⟨(ST.W[i]'(by rw [ST_len]; exact hi), i), List.mem_zipIdx_iff_getElem?.2 (by simp), rfl⟩

theorem seedL_mat (z : Int) : Mt (letM RB 12 (seedL z)) =
    if z = 1 then CFSG.Sporadic.Fi23.mA else if z = -1 then CFSG.Sporadic.Fi23.mA⁻¹
    else if z = 2 then CFSG.Sporadic.Fi23.mB else CFSG.Sporadic.Fi23.mB⁻¹ := by
  rw [mA_eq, mB_eq]
  unfold seedL
  by_cases h1 : z = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : z = -1
    · rw [ite_eq_left h2, ite_eq_left h2, letM_mat (by decide)]
      rfl
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : z = 2
      · rw [ite_eq_left h3, ite_eq_left h3]
        rfl
      · rw [ite_eq_right h3, ite_eq_right h3, letM_mat (by decide)]
        rfl

theorem imgL_mat {z : Int} (hz : z ≠ 0 ∧ z.natAbs ≤ 10) : Mt (letM RB 12 (imgL z)) =
    if 0 < z then M ((z - 1).toNat + 1) else (M ((-z - 1).toNat + 1))⁻¹ := by
  unfold imgL
  by_cases h : 0 < z
  · rw [ite_eq_left h, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, letM_mat (by simp only; omega)]
    rfl

open Certificates in
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge.Fi23GPL.Native in
theorem facts : imgWords.size = 10 ∧ surjWords.size = 2 ∧
    (∀ w ∈ surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10) ∧
    ∃ X : ℕ → Matrix (Fin 253) (Fin 253) (ZMod 3),
    (∀ k < 10, X k = (imgWords[k]!.map fun z =>
      if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹).prod) ∧
    (∀ v ∈ rels, (v.map fun l => if l.2 then X l.1 else (X l.1)⁻¹).prod = 1) ∧
    (surjWords[0]!.map fun z => if 0 < z then X (z - 1).toNat else (X (-z - 1).toNat)⁻¹).prod =
      mA ∧
    (surjWords[1]!.map fun z => if 0 < z then X (z - 1).toNat else (X (-z - 1).toNat)⁻¹).prod =
      mB := by
  have hIl : IT.W.toArray.size = 10 := by rw [List.size_toArray, IT_len]
  have hSl : ST.W.toArray.size = 2 := by rw [List.size_toArray, ST_len]
  have hlet : ∀ w ∈ surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10 := by
    rw [surj_eq]
    intro w hw
    exact ST_letters w (List.mem_toArray.1 hw)
  refine ⟨by rw [img_eq]; exact hIl, by rw [surj_eq]; exact hSl, hlet,
    fun k => M (k + 1), ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : k < IT.W.toArray.size := by rw [hIl]; exact hk
    change M (k + 1) = _
    rw [img_eq, getElem!_pos IT.W.toArray k hk', List.getElem_toArray]
    refine Eq.trans (word_eq (by omega) (img_mem hk)).symm ?_
    rw [List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro z _
    exact seedL_mat z
  · intro v hv
    have hv' : v ∈ relsX := by
      unfold relsX
      exact List.mem_append_left _ (List.mem_append_left _ hv)
    refine Eq.trans ?_ (rels_one v hv')
    apply congrArg
    apply List.map_congr_left
    intro x hx
    rw [letM_mat (bounded v hv' x hx)]
  · have hi : 0 < ST.W.toArray.size := by rw [hSl]; decide
    rw [surj_eq, getElem!_pos ST.W.toArray 0 hi, List.getElem_toArray]
    refine Eq.trans ?_ ((word_eq (g := 10) (by decide) (surj_mem (i := 0) (by decide))).trans
      mA_eq.symm)
    rw [List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro z hz
    change _ = Mt (letM RB 12 (imgL z))
    rw [imgL_mat (ST_letters _ (List.getElem_mem _) z hz)]
  · have hi : 1 < ST.W.toArray.size := by rw [hSl]; decide
    rw [surj_eq, getElem!_pos ST.W.toArray 1 hi, List.getElem_toArray]
    refine Eq.trans ?_ ((word_eq (g := 11) (by decide) (surj_mem (i := 1) (by decide))).trans
      mB_eq.symm)
    rw [List.map_map]
    apply congrArg
    apply List.map_congr_left
    intro z hz
    change _ = Mt (letM RB 12 (imgL z))
    rw [imgL_mat (ST_letters _ (List.getElem_mem _) z hz)]

end CertificateChecks.KernelSpor.Fi23Rels

end
