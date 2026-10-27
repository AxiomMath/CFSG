module

public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Sporadic.J4.QT2ARadNative
import Certificates.Kernel.J4Q.Strs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.QG CFSG.Sporadic.J4.QT2A.qGenW
#j4q_strs CFSG.KD.J4Q.Y5W CFSG.Sporadic.J4.QT2A.y5w
#j4q_strs CFSG.KD.J4Q.Y7W CFSG.Sporadic.J4.QT2A.y7w
#j4q_strs CFSG.KD.J4Q.Y11W CFSG.Sporadic.J4.QT2A.y11w
#j4q_strs CFSG.KD.J4Q.ADW CFSG.Sporadic.J4.QT2A.aDw
#j4q_strs CFSG.KD.J4Q.BDW CFSG.Sporadic.J4.QT2A.bDw

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] noncomputable def G5 : List Nat := [L0, L1, L2] ++ [A, B]

@[expose] noncomputable def G5i : List Nat := [L0i, L1i, L2i] ++ [Ai, Bi]

theorem locMats_size : (locMats ()).size = 3 := by simp [locMats, localWords]

theorem locInvs_size : (locInvs ()).size = 3 := by simp [locInvs, locMats, localWords]

theorem g5_wf (k : Nat) : WfA ((g5Mats ())[k]?.getD (idRows ())) :=
  (gens_append locMats_size loc_gens base_gens k).1

theorem g5i_wf (k : Nat) : WfA ((g5Invs ())[k]?.getD (idRows ())) :=
  (gens_append locInvs_size loc_invs base_invs k).1

theorem wR_enc (w : List Int) : WfA (wR w) ∧ encR (wR w) = wordJ c rm one G5 G5i w :=
  enc_wordRows hK (gens_append locMats_size loc_gens base_gens)
    (gens_append locInvs_size loc_invs base_invs) w

theorem invW_eq (w : List Int) : invW w = negRev w := by
  rw [negRev, negRevOnto_eq, List.append_nil]
  rfl

@[expose] noncomputable def qGenK : List (List Int) :=
  [w5K QG.s0, w5K ((QG.s1 ++ QG.s2) ++ QG.s3), w5K (QG.s4 ++ QG.s5),
    w5K ((QG.s6 ++ QG.s7) ++ QG.s8), w5K (QG.s9 ++ QG.s10), w5K (QG.s11 ++ QG.s12),
    w5K (QG.s13 ++ QG.s14), w5K ((QG.s15 ++ QG.s16) ++ QG.s17), w5K ((QG.s18 ++ QG.s19) ++ QG.s20),
    w5K (QG.s21 ++ QG.s22),
    w5K (QG.s23 ++ QG.s24), w5K (QG.s25 ++ QG.s26)]

theorem qGenW_eq : qGenW = qGenK := by
  rw [QG.eq]
  simp only [← String.ofList_append, w5_ofList]
  rfl

@[expose] noncomputable def y5K : List Int := w5K (Y5W.s0 ++ Y5W.s1)

@[expose] noncomputable def y7K : List Int := w5K (Y7W.s0 ++ Y7W.s1)

@[expose] noncomputable def y11K : List Int := w5K Y11W.s0

@[expose] noncomputable def aK : List Int := w5K ADW.s0

@[expose] noncomputable def bK : List Int :=
  w5K (((((BDW.s0 ++ BDW.s1) ++ BDW.s2) ++ BDW.s3) ++ BDW.s4) ++ BDW.s5)

theorem y5w_eq : y5w = y5K := by
  rw [Y5W.eq, ← String.ofList_append]
  exact w5_ofList _

theorem y7w_eq : y7w = y7K := by
  rw [Y7W.eq, ← String.ofList_append]
  exact w5_ofList _

theorem y11w_eq : y11w = y11K := by
  rw [Y11W.eq]
  exact w5_ofList _

theorem aDw_eq : aDw = aK := by
  rw [ADW.eq]
  exact w5_ofList _

theorem bDw_eq : bDw = bK := by
  rw [BDW.eq]
  simp only [← String.ofList_append]
  exact w5_ofList _

theorem y5R_enc : WfA (y5R ()) ∧ encR (y5R ()) = powJ c rm one (wordJ c rm one G5 G5i y5K) y5e :=
  ⟨wf_powRows (wR_enc _).1 _, by rw [y5R, enc_powRows hK (wR_enc _).1, (wR_enc _).2, y5w_eq]⟩

theorem y7R_enc : WfA (y7R ()) ∧ encR (y7R ()) = powJ c rm one (wordJ c rm one G5 G5i y7K) y7e :=
  ⟨wf_powRows (wR_enc _).1 _, by rw [y7R, enc_powRows hK (wR_enc _).1, (wR_enc _).2, y7w_eq]⟩

theorem y11R_enc :
    WfA (y11R ()) ∧ encR (y11R ()) = powJ c rm one (wordJ c rm one G5 G5i y11K) y11e :=
  ⟨wf_powRows (wR_enc _).1 _, by rw [y11R, enc_powRows hK (wR_enc _).1, (wR_enc _).2, y11w_eq]⟩

theorem wR_qWordG (sub : List Nat) (t : Nat) :
    wR (qWordG sub t) =
      selRows (fun j => wR (qGenW.getD (sub.getD j 0) [])) t (List.range 6) (idRows ()) := by
  unfold qWordG wR
  rw [wordRows_flatMap g5_wf g5i_wf]
  exact foldl_sel g5_wf g5i_wf (fun j => qGenW.getD (sub.getD j 0) []) t _ _ wf_idRows

theorem invW_flatMap {β : Type} (f : β → List Int) :
    ∀ L : List β, invW (L.flatMap f) = L.reverse.flatMap fun i => invW (f i)
  | [] => rfl
  | x :: L => by
    rw [List.flatMap_cons, List.reverse_cons, List.flatMap_append, ← invW_flatMap f L,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [invW, List.reverse_append, List.map_append]

theorem wR_invW_qWordG (sub : List Nat) (t : Nat) :
    wR (invW (qWordG sub t)) = selRows (fun j => wR (invW (qGenW.getD (sub.getD j 0) []))) t
      (List.range 6).reverse (idRows ()) := by
  unfold qWordG
  rw [invW_flatMap]
  have : (fun i => invW (if t.testBit i then qGenW.getD (sub.getD i 0) [] else [])) =
      fun i => if t.testBit i then invW (qGenW.getD (sub.getD i 0) []) else [] := by
    funext i
    split <;> rfl
  rw [this]
  unfold wR
  rw [wordRows_flatMap g5_wf g5i_wf]
  exact foldl_sel g5_wf g5i_wf (fun j => invW (qGenW.getD (sub.getD j 0) [])) t _ _ wf_idRows

theorem conjDistinct_of (w : Nat → List Int) (p pi : Nat → Nat)
    (hp : ∀ t, encR (wR (w t)) = p t) (hpi : ∀ t, encR (wR (invW (w t))) = pi t)
    (X : Array V2) (x : Nat) (hX : WfA X) (hx : encR X = x)
    (h : strictB x (fun x => distinctK (smapK (fun t => mulJ c rm (mulJ c rm (p t) x) (pi t))
      (rangeK 64))) = true) :
    conjDistinct w X = true := by
  have hF : ∀ t, WfA (mulRows (mulRows (wR (w t)) X) (wR (invW (w t)))) ∧
      encR (mulRows (mulRows (wR (w t)) X) (wR (invW (w t)))) =
        mulJ c rm (mulJ c rm (p t) x) (pi t) :=
    fun t => ⟨wf_mulRows (wf_mulRows (wR_enc _).1 hX) (wR_enc _).1, by
      rw [enc_mulRows hK (wf_mulRows (wR_enc _).1 hX) (wR_enc _).1,
        enc_mulRows hK (wR_enc _).1 hX, hp, hpi, hx]⟩
  have hl : (List.zip ((List.range 64).map fun t => wR (w t))
      ((List.range 64).map fun t => wR (invW (w t)))).map (fun p => mulRows (mulRows p.1 X) p.2) =
      (List.range 64).map (fun t => mulRows (mulRows (wR (w t)) X) (wR (invW (w t)))) := by
    rw [List.zip_map', List.map_map]
    rfl
  have hwf : ∀ y ∈ (List.range 64).map (fun t => mulRows (mulRows (wR (w t)) X) (wR (invW (w t)))),
      WfA y := by
    intro y hy
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hy
    exact (hF t).1
  unfold conjDistinct
  simp only []
  rw [hl, Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun y hy => wf_bool (hwf y hy), ?_⟩
  rw [allDistinct_enc _ hwf, List.map_map]
  rw [strictB_eq, smapK_eq, rangeK_eq] at h
  have : (encR ∘ fun t => mulRows (mulRows (wR (w t)) X) (wR (invW (w t)))) =
      (fun t => mulJ c rm (mulJ c rm (p t) x) (pi t)) := by
    funext t
    exact (hF t).2
  rw [this]
  exact h

end CertificateChecks.KernelJ4Q

end
