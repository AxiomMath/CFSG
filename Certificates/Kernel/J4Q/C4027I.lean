module

public import Certificates.Kernel.J4Q.X0OrbOk
public import Certificates.Kernel.J4Q.X0Conj
public import Certificates.Kernel.J4Q.ListAux
public import Certificates.Kernel.J4Q.LocVec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] noncomputable def invQ (m : Nat) : Bool := andB (notB (Nat.beq m one)) (Nat.beq (mulJ c rm m m) one)

theorem xinv_chk : eqLK ((List.range 6720).filter fun k => inLK k XINV) XINV = true := by quickRfl

theorem xinvc_chk :
    (XINV.all fun k => orB (inLK (CFSG.KD.X0O.MSF k) CT) (inLK (CFSG.KD.X0O.MSF k) CZ)) = true := by
  quickRfl

theorem xinv_len : (XINV.length == 91) = true := by quickRfl

theorem ct_eq : (List.range 84).map (getN one CT) = CT := eqLK_spec (by quickRfl)

theorem cz_eq : (List.range 7).map (getN one CZ) = CZ := eqLK_spec (by quickRfl)

theorem inLK_mem {x : Nat} : ∀ {l : List Nat}, inLK x l = true → x ∈ l
  | [], h => (Bool.false_ne_true h).elim
  | y :: l, h => by
    change orB (Nat.beq x y) (inLK x l) = true at h
    rw [orB_eq'', Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (inLK_mem h)

theorem xboolEq_spec {a b : Bool} (h : xBoolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact (Bool.false_ne_true h).elim

theorem invs_filter :
    (x0Orb.mats.toList.filter fun M => !eqRows M idRows && eqRows (mulRows M M) idRows).map encR =
      XINV.map CFSG.KD.X0O.MSF := by
  obtain ⟨-, hmap, hwf⟩ := x0Orb_ok
  have hq : ∀ X ∈ x0Orb.mats.toList, (!eqRows X idRows && eqRows (mulRows X X) idRows) = invQ (encR X) := by
    intro X hX
    rw [eqRows_of ⟨hwf X hX, rfl⟩ (id_enc hK),
      eqRows_of (mul_enc hK ⟨hwf X hX, rfl⟩ ⟨hwf X hX, rfl⟩) (id_enc hK), invQ, andB_eq, notB_eq]
  rw [filter_map_comm (q := invQ) (f := encR) _ hq, hmap, List.filter_map]
  refine congrArg (List.map CFSG.KD.X0O.MSF) ?_
  have hx : ((List.range 6720).filter fun k => inLK k XINV) = XINV := eqLK_spec xinv_chk
  rw [← hx]
  apply List.filter_congr
  intro k hk
  have h := xDer_spec (List.mem_range.1 hk)
  unfold xDerK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact xboolEq_spec h.2

theorem mem_conj_any {L : Array (Array V2)} {Ms : List Nat} {n : Nat} (hm : L.toList.map encR = (List.range n).map (getN one Ms))
    (hw : ∀ X ∈ L.toList, WfA X) (hMs : (List.range n).map (getN one Ms) = Ms) {y : Array V2} (hy : WfA y)
    (hin : encR y ∈ Ms) : L.any (eqRows y) = true := by
  rw [← Array.any_toList, List.any_eq_true]
  rw [← hMs, ← hm] at hin
  obtain ⟨z, hz, hze⟩ := List.mem_map.1 hin
  refine ⟨z, hz, ?_⟩
  rw [eqRows_of ⟨hy, rfl⟩ ⟨hw z hz, rfl⟩, hze]
  exact Nat.beq_refl _

theorem x0invs_ok : chkX0Invs = true := by
  obtain ⟨-, -, hwf⟩ := x0Orb_ok
  obtain ⟨-, hmT, hwT⟩ := x0ConjT_ok
  obtain ⟨-, hmZ, hwZ⟩ := x0ConjZ_ok
  have hf := invs_filter
  unfold chkX0Invs x0Invs
  rw [Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.2 fun y hy => ?_⟩
  · have hl := congrArg List.length hf
    rw [List.length_map, List.length_map] at hl
    rw [hl]
    exact xinv_len
  · have hyl := List.mem_map_of_mem (f := encR) hy
    rw [hf] at hyl
    obtain ⟨k, hk, hkk⟩ := List.mem_map.1 hyl
    have hc := List.all_eq_true.1 xinvc_chk k hk
    rw [orB_eq'', Bool.or_eq_true, hkk] at hc
    have hwy := hwf y (List.mem_filter.1 hy).1
    rw [Bool.or_eq_true]
    rcases hc with hc | hc
    · exact Or.inl (mem_conj_any hmT hwT ct_eq hwy (inLK_mem hc))
    · exact Or.inr (mem_conj_any hmZ hwZ cz_eq hwy (inLK_mem hc))

end CertificateChecks.KernelJ4Q

end
