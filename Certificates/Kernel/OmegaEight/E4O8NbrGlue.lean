module

public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.OmegaEight.E4O8NbrK
public import Certificates.Data.E4QuatO8Two
public import Certificates.Data.E4QuatO8Three

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4O8

theorem any_eqA_pk {x : Nat} (hx : cn x = true) : ∀ L : List Nat, (∀ y ∈ L, cn y = true) →
    (L.map (unpack 360 9)).any (fun y => eqA 360 (unpack 360 9 x) y) = L.any (Nat.beq x)
  | [], _ => rfl
  | y :: L, hL => by
    rw [List.map_cons, List.any_cons, List.any_cons, eqA_pc hx (hL y List.mem_cons_self),
      any_eqA_pk hx L fun z hz => hL z (List.mem_cons_of_mem _ hz)]

theorem memA_pk {L : List Nat} {x : Nat} (hL : ∀ y ∈ L, cn y = true) (hx : cn x = true) :
    CFSG.ClassicalInvolution.Q3.TL4.E4A.memA 360 (L.map (unpack 360 9)) (unpack 360 9 x) = e4Mem L x := by
  unfold CFSG.ClassicalInvolution.Q3.TL4.E4A.memA e4Mem
  exact any_eqA_pk hx L hL

theorem conjA_pk {c x : Nat} (hc : cn c = true) (hci : cn (pinv c) = true) (hp : pm c = true)
    (hx : cn x = true) : CFSG.ClassicalInvolution.Q3.TL4.E4A.conjA 360 (unpack 360 9 c) (unpack 360 9 x) = unpack 360 9 (cj c x) := by
  unfold CFSG.ClassicalInvolution.Q3.TL4.E4A.conjA
  rw [invCand_pinv hp, compA_pc hc hx, compA_pc (cn_pc hc hx) hci]
  rfl

theorem normsA_pk {L : List Nat} {i j h : Nat} (hL : ∀ y ∈ L, cn y = true) (hi : cn i = true)
    (hj : cn j = true) (hh : cn h = true) (hhi : cn (pinv h) = true) (hp : pm h = true) :
    CFSG.ClassicalInvolution.Q3.TL4.E4A.normsA 360 (L.map (unpack 360 9)) (unpack 360 9 i) (unpack 360 9 j) (unpack 360 9 h) =
      e4Norms L i j h := by
  unfold CFSG.ClassicalInvolution.Q3.TL4.E4A.normsA e4Norms
  rw [conjA_pk hh hhi hp hi, conjA_pk hh hhi hp hj, memA_pk hL (cn_cj hh hhi hi),
    memA_pk hL (cn_cj hh hhi hj)]

theorem e4_not_of {b : Bool} (h : bIf(b, false, true) = true) : (!b) = true := by
  revert h
  cases b <;> decide

theorem e4Pm_iff {p : Nat} : e4Pm p = true ↔ pm p = true ∧ cn (pinv p) = true := by
  unfold e4Pm
  exact bAnd_iff _ _

theorem edgeCheckA_pk {L : List Nat} {i j g : Nat} (hL : ∀ y ∈ L, cn y = true) (hi : cn i = true)
    (hj : cn j = true) (hg : cn g = true) (hgi : cn (pinv g) = true) (hp : pm g = true)
    (h1 : e4Pm (cj g i) = true) (h2 : e4Pm (cj g j) = true) :
    CFSG.ClassicalInvolution.Q3.TL4.E4A.edgeCheckA 360 (L.map (unpack 360 9)) (unpack 360 9 i) (unpack 360 9 j) (unpack 360 9 g) =
      e4Edge L i j g := by
  obtain ⟨p1, c1⟩ := e4Pm_iff.1 h1
  obtain ⟨p2, c2⟩ := e4Pm_iff.1 h2
  unfold CFSG.ClassicalInvolution.Q3.TL4.E4A.edgeCheckA e4Edge
  rw [conjA_pk hg hgi hp hi, conjA_pk hg hgi hp hj, normsA_pk hL hi hj hg hgi hp,
    normsA_pk hL hi hj (cn_cj hg hgi hi) c1 p1, normsA_pk hL hi hj (cn_cj hg hgi hj) c2 p2]

theorem e4_facts : lettersK 17 e4UW = true ∧ cn e4U = true ∧ lettersK 17 om0VW = true ∧
    cn om0V = true ∧ cn (mainK 0) = true ∧ xA 0 = unpack 360 9 (mainK 0) := by
  have hk := kE4Nbr
  simp only [bAnd_iff] at hk
  have h0 := kOm0
  simp only [bAnd_iff] at h0
  obtain ⟨ex, cx, -⟩ := main_ok (by norm_num : 0 < 5)
  exact ⟨hk.1, hk.2.1, h0.2.1, h0.2.2.1, cx, ex⟩

theorem e4L_cn : ∀ y ∈ e4L, cn y = true := by
  obtain ⟨-, cu, -, cv, cx, -⟩ := e4_facts
  intro y hy
  simp only [e4L, e4Q, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [cn_pid, cx, cu, cn_pc cu cx, cv, cn_pc cv cx, cn_pc cu cv, cn_pc (cn_pc cu cv) cx]

theorem u0A_pk : u0A () = unpack 360 9 e4U := omegaW_eq e4_facts.1

theorem v0A_pk : v0A () = unpack 360 9 om0V := omegaW_eq e4_facts.2.2.1

theorem L0A_pk : L0A () = e4L.map (unpack 360 9) := by
  obtain ⟨-, cu, -, cv, cx, ex⟩ := e4_facts
  unfold L0A CFSG.ClassicalInvolution.Q3.TL4.E4A.q8A
  rw [ex, u0A_pk, v0A_pk, idA_eq, compA_pc cu cx, compA_pc cv cx, compA_pc cu cv,
    compA_pc (cn_pc cu cv) cx]
  rfl

theorem root_facts {l : Nat} (hl : l < 8) : (rootA ()).getD l (idA 360) = unpack 360 9 (AP.S l) ∧
    cn (AP.S l) = true ∧ pm (AP.S l) = true ∧ cn (pinv (AP.S l)) = true := by
  have hk := kOm0
  simp only [bAnd_iff] at hk
  have h := allN_spec hk.1 l hl
  simp only [bAnd_iff] at h
  have hs := kStrC
  simp only [bAnd_iff] at hs
  refine ⟨?_, allN_spec hs.1 l (by omega), h.1, h.2⟩
  have e := gen_get (by omega : l < 10)
  rw [rootA, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  exact e

theorem edge_at {l : Nat} (hl : l < 8) (h : e4EdgeAt (AP.S l) = true) :
    CFSG.ClassicalInvolution.Q3.TL4.E4A.edgeCheckA 360 (L0A ()) (u0A ()) (v0A ()) ((rootA ()).getD l (idA 360)) = true := by
  obtain ⟨-, cu, -, cv, -, -⟩ := e4_facts
  obtain ⟨e, c, p, i⟩ := root_facts hl
  unfold e4EdgeAt at h
  simp only [bAnd_iff] at h
  rw [L0A_pk, u0A_pk, v0A_pk, e, edgeCheckA_pk e4L_cn cu cv c i p h.1 h.2.1]
  exact h.2.2

theorem diff_at {a b : Nat} (ha : a < 8) (hb : b < 8) (h : e4DiffAt (AP.S a) (AP.S b) = true) :
    (!CFSG.ClassicalInvolution.Q3.TL4.E4A.normsA 360 (L0A ()) (u0A ()) (v0A ())
      (compA 360 (invCand 360 ((rootA ()).getD a (idA 360))) ((rootA ()).getD b (idA 360)))) =
      true := by
  obtain ⟨-, cu, -, cv, -, -⟩ := e4_facts
  obtain ⟨ea, ca, pa, ia⟩ := root_facts ha
  obtain ⟨eb, cb, -, -⟩ := root_facts hb
  unfold e4DiffAt at h
  simp only [bAnd_iff] at h
  obtain ⟨hp, hn⟩ := h
  obtain ⟨p1, c1⟩ := e4Pm_iff.1 hp
  rw [L0A_pk, u0A_pk, v0A_pk, ea, eb, invCand_pinv pa, compA_pc ia cb,
    normsA_pk e4L_cn cu cv (cn_pc ia cb) c1 p1]
  exact e4_not_of hn

theorem twoCheck_k : twoCheck () = true := by
  have hk := kE4Nbr
  simp only [bAnd_iff] at hk
  obtain ⟨-, -, h0, h4, -, d04, -, -⟩ := hk
  unfold twoCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨edge_at (by norm_num) h0, edge_at (by norm_num) h4⟩, diff_at (by norm_num) (by norm_num) d04⟩

theorem threeCheck_k : threeCheck () = true := by
  have hk := kE4Nbr
  simp only [bAnd_iff] at hk
  obtain ⟨-, -, -, -, h6, -, d06, d46⟩ := hk
  unfold threeCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨edge_at (by norm_num) h6, diff_at (by norm_num) (by norm_num) d06⟩,
    diff_at (by norm_num) (by norm_num) d46⟩

end CertificateChecks.KernelO8

end
