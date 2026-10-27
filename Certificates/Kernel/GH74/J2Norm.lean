module

public import Certificates.Kernel.GH74.J2EvG
public import CFSG.GH74.Generic.S45.LEvSporJ2Spec
public import Certificates.Data.GH74IvkCentJ2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2Norm

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74 CertificateChecks.KernelGH74.J2Ev
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn
open CFSG.Certificates CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover

theorem conj_comm_iff {G : Type*} [Group G] (h a x : G) :
    x * (h * a * h⁻¹) = h * a * h⁻¹ * x ↔ h⁻¹ * x * h * a = a * (h⁻¹ * x * h) := by
  rw [show h⁻¹ * x * h * a = h⁻¹ * (x * (h * a * h⁻¹)) * h by group,
    show a * (h⁻¹ * x * h) = h⁻¹ * (h * a * h⁻¹ * x) * h by group, mul_left_inj, mul_right_inj]

noncomputable def pA : Equiv.Perm (Fin 315) := tp 315 j2KbA
noncomputable def pB : Equiv.Perm (Fin 315) := tp 315 j2KbB
noncomputable def pT : Equiv.Perm (Fin 315) := tp 315 j2Row2A.rep
noncomputable def pS : Equiv.Perm (Fin 315) := tp 315 j2Row2B.rep
noncomputable def pH : Equiv.Perm (Fin 315) := tp 315 (tabT (unpack 315 9 hK))
noncomputable def pV : Equiv.Perm (Fin 315) := tp 315 j2VA
noncomputable def KB : Subgroup (Equiv.Perm (Fin 315)) :=
  closure (tp 315 '' {x | x ∈ j2KbGens.toArray})

theorem hn : (315 : Nat) < 2 ^ 32 := by norm_num

theorem hfacts : canonK 315 9 (mask 9) (315 * 9) hK = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2HI 0) = true ∧ sK hK = true ∧
    invEqK 315 9 (mask 9) (315 * 9) hK (J2HI 0) = true ∧
    Nat.beq (pc (pc hK (F 31)) (J2HI 0)) (J2XT 0) = true := by
  have h := h_ok
  simp only [bAnd_iff] at h
  exact h

theorem xc {j : Nat} (hj : j < 8) : canonK 315 9 (mask 9) (315 * 9) (J2XT j) = true := (xp hj).1

theorem repX {j : Nat} (hj : j < 8) :
    Rep 315 (tabT (unpack 315 9 (J2XT j))) (tp 315 (tabT (unpack 315 9 (J2XT j)))) :=
  rep_tp (permOK_unpack (xc hj) (xp hj).2.2)

theorem repA : Rep 315 (tabT (unpack 315 9 (J2XT 0))) pA := by
  rw [pA, x_tabs.1]
  exact repX (by norm_num)

theorem repB : Rep 315 (tabT (unpack 315 9 (J2XT 1))) pB := by
  rw [pB, x_tabs.2.1]
  exact repX (by norm_num)

theorem repV : Rep 315 (tabT (unpack 315 9 (J2XT 2))) pV := by
  rw [pV, x_tabs.2.2.1]
  exact repX (by norm_num)

theorem repT : Rep 315 (tabT (unpack 315 9 (F 31))) pT := by
  rw [pT, show j2Row2A.rep = j2CentTbl 31 from rfl, ← tabF (by norm_num : 31 < 42)]
  exact rep_tp (permF (by norm_num))

theorem repS : Rep 315 (tabT (unpack 315 9 (F 17))) pS := by
  rw [pS, show j2Row2B.rep = j2CentTbl 17 from rfl, ← tabF (by norm_num : 17 < 42)]
  exact rep_tp (permF (by norm_num))

theorem repU : Rep 315 (tabT (unpack 315 9 (F 0))) j2u := by
  rw [j2u, j2OuterTbl, ← tabF (by norm_num : 0 < 42)]
  exact rep_tp (permF (by norm_num))

theorem repH : Rep 315 (tabT (unpack 315 9 hK)) pH := rep_tp (permOK_unpack hfacts.1 hfacts.2.2.2.1)

theorem repHI : Rep 315 (tabT (unpack 315 9 (J2HI 0))) pH⁻¹ := by
  have := rep_invT_of_rep hn repH
  rwa [invT_unpack (by norm_num) hfacts.2.2.2.1] at this

theorem cB : canonK 315 9 (mask 9) (315 * 9) bK = true :=
  CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hfacts.2.1 (xc (by norm_num))) hfacts.1

theorem repB' : Rep 315 (tabT (unpack 315 9 bK)) (pH⁻¹ * pB * pH) := by
  unfold bK pc
  rw [← compT_unpack (CFSG.KC.BfsPin.canonK_pcomp hfacts.2.1 (xc (by norm_num))) hfacts.1,
    ← compT_unpack hfacts.2.1 (xc (by norm_num))]
  exact Rep.compT (Rep.compT repHI repB) repH

theorem hA_eq : pH * pT * pH⁻¹ = pA := by
  have hr : Rep 315 (tabT (unpack 315 9 (pc (pc hK (F 31)) (J2HI 0)))) (pH * pT * pH⁻¹) := by
    unfold pc
    rw [← compT_unpack (CFSG.KC.BfsPin.canonK_pcomp hfacts.1 (Fc (by norm_num))) hfacts.2.1,
      ← compT_unpack hfacts.1 (Fc (by norm_num))]
    exact Rep.compT (Rep.compT repH repT) repHI
  rw [Nat.eq_of_beq_eq_true hfacts.2.2.2.2] at hr
  exact rep_unique hr repA


theorem pH_mem : pH ∈ j2P :=
  (j2_groupData.sift _ _ repH).1 (by rw [sift_eq hfacts.1]; exact hfacts.2.2.1)

noncomputable def CT : Subgroup (Equiv.Perm (Fin 315)) :=
  j2P ⊓ centralizer ({pT} : Set (Equiv.Perm (Fin 315)))

theorem mem_CT {c : Equiv.Perm (Fin 315)} : c ∈ CT ↔ c ∈ j2P ∧ c * pT = pT * c := by
  unfold CT
  rw [mem_inf, mem_centralizer_singleton_iff]

theorem enumsCT : EnumsSub 315 j2C2A CT := by
  unfold CT pT
  exact (j2_C2A_enums c2A_ok).1

theorem cardCT : Nat.card CT = j2C2A.size := by
  unfold CT pT
  rw [(j2_rows_spec.1 j2Row2A j2Row2A_mem).2.2.2.2, j2Row2A_centOrder, c2_arr, hRec_size]
  rfl

theorem c2_get {k : Nat} (hk : k < j2C2A.size) : j2C2A[k]! = tabT (unpack 315 9 (J2C2.T k)) := by
  have hk' : k < J2C2.cnt := by rw [c2_arr, hRec_size] at hk; exact hk
  rw [c2_arr]
  exact hRec_get hk'

theorem conj_back (c : Equiv.Perm (Fin 315)) : pH⁻¹ * (pH * c * pH⁻¹) * pH = c := by group

theorem conj_fwd (x : Equiv.Perm (Fin 315)) : pH * (pH⁻¹ * x * pH) * pH⁻¹ = x := by group

theorem conjI_mem {x : Equiv.Perm (Fin 315)} (hx : x ∈ j2P) : pH⁻¹ * x * pH ∈ j2P :=
  j2P.mul_mem (j2P.mul_mem (j2P.inv_mem pH_mem) hx) pH_mem

theorem conj_mem {x : Equiv.Perm (Fin 315)} (hx : x ∈ j2P) : pH * x * pH⁻¹ ∈ j2P :=
  j2P.mul_mem (j2P.mul_mem pH_mem hx) (j2P.inv_mem pH_mem)

theorem commA_iff (x : Equiv.Perm (Fin 315)) :
    x * pA = pA * x ↔ pH⁻¹ * x * pH * pT = pT * (pH⁻¹ * x * pH) := by
  have e := conj_comm_iff pH pT x
  rw [hA_eq] at e
  exact e

theorem commB_iff (x : Equiv.Perm (Fin 315)) :
    x * pB = pB * x ↔ pH⁻¹ * x * pH * (pH⁻¹ * pB * pH) = pH⁻¹ * pB * pH * (pH⁻¹ * x * pH) := by
  have e := conj_comm_iff pH (pH⁻¹ * pB * pH) x
  rw [show pH * (pH⁻¹ * pB * pH) * pH⁻¹ = pB by group] at e
  exact e

theorem cent_equiv (Q : Equiv.Perm (Fin 315) → Prop) (hQ : ∀ x, Q (pH⁻¹ * x * pH) ↔ Q x) :
    Nat.card {x : j2P // x * pA = pA * x ∧ x * pB = pB * x ∧ Q x} =
      Nat.card {c : CT // c * (pH⁻¹ * pB * pH) = pH⁻¹ * pB * pH * c ∧ Q c} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨pH⁻¹ * x.1 * pH, mem_CT.2 ⟨conjI_mem x.1.2, (commA_iff x.1).1 x.2.1⟩⟩,
        (commB_iff x.1).1 x.2.2.1, (hQ x.1).2 x.2.2.2⟩
      invFun := fun c => ⟨⟨pH * c.1 * pH⁻¹, conj_mem (mem_CT.1 c.1.2).1⟩,
        (commA_iff _).2 (by rw [conj_back]; exact (mem_CT.1 c.1.2).2),
        (commB_iff _).2 (by rw [conj_back]; exact c.2.1), (hQ _).1 (by rw [conj_back]; exact c.2.2)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (conj_fwd x.1.1))
      right_inv := fun c => Subtype.ext (Subtype.ext (conj_back c.1.1)) }

theorem inner_card :
    Nat.card {x : j2P // x * pA = pA * x ∧ x * pB = pB * x ∧ True} = 12 := by
  rw [cent_equiv (fun _ => True) (fun _ => Iff.rfl)]
  have e : Nat.card {c : CT // c * (pH⁻¹ * pB * pH) = pH⁻¹ * pB * pH * c ∧ True} =
      Nat.card {c : CT // c * (pH⁻¹ * pB * pH) = pH⁻¹ * pB * pH * c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => by simp)
  rw [e, card_eq_countP_of_enums enumsCT cardCT (p := fun T => commTT 315 T (tabT (unpack 315 9 bK)))
    (fun T g hT => commTT_iff hT repB'), c2_arr,
    countP_hRec (hi := 30) (q := fun i => pcommK 315 9 (J2C2.T i) bK) (by rfl)
      (fun i hi => by rw [commF (c2c hi) cB, pcommK_eq (c2c hi) cB]; rfl)]
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 c2_inner).1

theorem band_eq (a b : Bool) : (a && b) = bAnd(a, b) := by cases a <;> rfl

theorem orderOf_conjH (x : Equiv.Perm (Fin 315)) : orderOf (pH⁻¹ * x * pH) = orderOf x :=
  (SemiconjBy.orderOf_eq pH⁻¹ (x := x) (y := pH⁻¹ * x * pH) (by
    unfold SemiconjBy
    group)).symm

theorem inv_card :
    Nat.card {x : j2P // x * pA = pA * x ∧ x * pB = pB * x ∧
      orderOf (x : Equiv.Perm (Fin 315)) = 2} = 3 := by
  rw [cent_equiv (fun x => orderOf x = 2) (fun x => by rw [orderOf_conjH])]
  rw [card_eq_countP_of_enums enumsCT cardCT
    (p := fun T => commTT 315 T (tabT (unpack 315 9 bK)) && involOK 315 T)
    (P := fun c => c * (pH⁻¹ * pB * pH) = pH⁻¹ * pB * pH * c ∧ orderOf c = 2)
    (fun T g hT => by
      rw [Bool.and_eq_true, commTT_iff hT repB']
      exact and_congr_right fun _ =>
        ⟨orderOf_eq_two_of_involOK hn hT, involOK_of_orderOf hn hT⟩), c2_arr,
    countP_hRec (hi := 30) (q := fun i => bAnd(pcommK 315 9 (J2C2.T i) bK, involK (J2C2.T i)))
      (by rfl) (fun i hi => by
        rw [commF (c2c hi) cB, pcommK_eq (c2c hi) cB, involF (c2c hi), band_eq]
        rfl)]
  have h := c2_inner
  simp only [bAnd_iff] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem facts2 : J2Cn.commK (F 17) (J2XT 0) = true ∧ J2Cn.commK (F 17) (J2XT 1) = true ∧
    ∀ i < J2KB.cnt, bIf(bAnd(J2Cn.commK (J2KB.T i) (J2XT 0), J2Cn.commK (J2KB.T i) (J2XT 1)),
      Nat.beq (J2KB.T i) idK, true) = true := by
  have h := kb_center
  simp only [bAnd_iff] at h
  exact ⟨h.2.1, h.2.2, allN_spec h.1⟩

theorem kbT_canon {i : Nat} (hi : i < J2KB.cnt) : canonK 315 9 (mask 9) (315 * 9) (J2KB.T i) = true :=
  penumPt_canon (kb_pe i hi)

theorem s_comm : pS * pA = pA * pS ∧ pS * pB = pB * pS := by
  refine ⟨(commTT_iff repS repA).1 ?_, (commTT_iff repS repB).1 ?_⟩
  · rw [commF (Fc (by norm_num)) (xc (by norm_num))]
    exact facts2.1
  · rw [commF (Fc (by norm_num)) (xc (by norm_num))]
    exact facts2.2.1

theorem enumsK : EnumsSub 315 j2Kb KB := by
  unfold KB
  exact (enumOK_spec hn kb_enum).1

theorem center_K {m : Equiv.Perm (Fin 315)} (hm : m ∈ KB) (h1 : m * pA = pA * m)
    (h2 : m * pB = pB * m) : m = 1 := by
  obtain ⟨k, hk, hrk⟩ := enumsK.2 m hm
  have hk' : k < J2KB.cnt := by rw [kb_arr, hRec_size] at hk; exact hk
  rw [kb_arr, hRec_get hk'] at hrk
  have hT := kbT_canon hk'
  have c1 : J2Cn.commK (J2KB.T k) (J2XT 0) = true := by
    rw [← commF hT (xc (by norm_num))]
    exact (commTT_iff hrk repA).2 h1
  have c2 : J2Cn.commK (J2KB.T k) (J2XT 1) = true := by
    rw [← commF hT (xc (by norm_num))]
    exact (commTT_iff hrk repB).2 h2
  have h := facts2.2.2 k hk'
  rw [c1, c2] at h
  have e : J2KB.T k = pidn 315 9 := Nat.eq_of_beq_eq_true h
  rw [e, ← hid] at hrk
  exact rep_unique hrk (Rep.idT hn)

theorem genK {k : Equiv.Perm (Fin 315)} (hk : k ∈ tp 315 '' {x | x ∈ j2KbGens.toArray}) :
    k = pA ∨ k = pB := by
  obtain ⟨x, hx, rfl⟩ := hk
  have hx' : x ∈ j2KbGens := List.mem_toArray.1 hx
  simp only [j2KbGens, List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem pA_mem : pA ∈ KB := subset_closure ⟨j2KbA, by simp [j2KbGens], rfl⟩

theorem pB_mem : pB ∈ KB := subset_closure ⟨j2KbB, by simp [j2KbGens], rfl⟩

theorem KB_le : KB ≤ j2P := (j2_Kb_facts kb_ok).2.2.1

theorem cardKB : Nat.card KB = 60 := (j2_Kb_facts kb_ok).2.1

theorem mem_norm {x : Equiv.Perm (Fin 315)} (ha : x * pA * x⁻¹ ∈ KB) (hb : x * pB * x⁻¹ ∈ KB) :
    x ∈ normalizer (KB : Set (Equiv.Perm (Fin 315))) :=
  mem_normalizer_of_conj_le (conj_mem_closure fun k hk => by
    rcases genK hk with rfl | rfl
    · exact ha
    · exact hb)

theorem cent_of_gens {c : Equiv.Perm (Fin 315)} (ha : c * pA = pA * c) (hb : c * pB = pB * c) :
    ∀ m ∈ KB, c * m = m * c := by
  have hle : KB ≤ centralizer ({c} : Set (Equiv.Perm (Fin 315))) := by
    refine (closure_le _).2 fun k hk => ?_
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases genK hk with rfl | rfl
    · exact ha.symm
    · exact hb.symm
  intro m hm
  exact ((mem_centralizer_singleton_iff).1 (hle hm)).symm

theorem conj_kc {k c X : Equiv.Perm (Fin 315)} (hk : k ∈ KB) (hc : c * X = X * c) (hX : X ∈ KB) :
    k * c * X * (k * c)⁻¹ ∈ KB := by
  have e : k * c * X * (k * c)⁻¹ = k * (c * X) * c⁻¹ * k⁻¹ := by group
  rw [e, hc, show k * (X * c) * c⁻¹ * k⁻¹ = k * X * k⁻¹ by group]
  exact KB.mul_mem (KB.mul_mem hk hX) (KB.inv_mem hk)

theorem norm_ge :
    720 ≤ Nat.card {x : j2P // x * pA * x⁻¹ ∈ KB ∧ x * pB * x⁻¹ ∈ KB} := by
  let f : KB × {x : j2P // x * pA = pA * x ∧ x * pB = pB * x ∧ True} →
      {x : j2P // x * pA * x⁻¹ ∈ KB ∧ x * pB * x⁻¹ ∈ KB} := fun kc =>
    ⟨⟨kc.1.1 * kc.2.1.1, j2P.mul_mem (KB_le kc.1.2) kc.2.1.2⟩,
      conj_kc kc.1.2 kc.2.2.1 pA_mem, conj_kc kc.1.2 kc.2.2.2.1 pB_mem⟩
  have hf : Function.Injective f := by
    rintro ⟨k, c⟩ ⟨k', c'⟩ h
    have e : k.1 * c.1.1 = k'.1 * c'.1.1 := congrArg (fun z => z.1.1) h
    have hm : k'.1⁻¹ * k.1 = c'.1.1 * c.1.1⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
      group
    have hmK : k'.1⁻¹ * k.1 ∈ KB := KB.mul_mem (KB.inv_mem k'.2) k.2
    have hA : Commute (c'.1.1 * c.1.1⁻¹) pA := Commute.mul_left c'.2.1 (Commute.inv_left c.2.1)
    have hB : Commute (c'.1.1 * c.1.1⁻¹) pB :=
      Commute.mul_left c'.2.2.1 (Commute.inv_left c.2.2.1)
    rw [← hm] at hA hB
    have h1 := center_K hmK hA hB
    have hk : k.1 = k'.1 := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    have hc : c.1.1 = c'.1.1 := by
      rw [hk] at e
      exact mul_left_cancel e
    exact Prod.ext (Subtype.ext hk) (Subtype.ext (Subtype.ext hc))
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, cardKB, inner_card] at h
  exact h

theorem s_mem : pS ∈ j2P := j2_row_mem_P j2Row2B_mem j2Row2B_outer

theorem s_order : orderOf pS = 2 := (j2_rows_spec.1 j2Row2B j2Row2B_mem).2.1

theorem conj_s_mem {n : Equiv.Perm (Fin 315)} (hn' : n ∈ j2P) (ha : n * pA * n⁻¹ ∈ KB)
    (hb : n * pB * n⁻¹ ∈ KB) :
    (n * pS * n⁻¹) * pA = pA * (n * pS * n⁻¹) ∧ (n * pS * n⁻¹) * pB = pB * (n * pS * n⁻¹) ∧
      orderOf (n * pS * n⁻¹) = 2 := by
  have hN := mem_norm ha hb
  have hNi := (normalizer (KB : Set (Equiv.Perm (Fin 315)))).inv_mem hN
  have hc := cent_of_gens s_comm.1 s_comm.2
  have key : ∀ X ∈ KB, (n * pS * n⁻¹) * X = X * (n * pS * n⁻¹) := by
    intro X hX
    have hq : n⁻¹ * X * n⁻¹⁻¹ ∈ KB := (mem_normalizer_iff.1 hNi X).1 hX
    have hsq := hc _ hq
    calc n * pS * n⁻¹ * X = n * (pS * (n⁻¹ * X * n⁻¹⁻¹)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * X * n⁻¹⁻¹) * pS) * n⁻¹ := by rw [hsq]
      _ = X * (n * pS * n⁻¹) := by group
  refine ⟨key pA pA_mem, key pB pB_mem, ?_⟩
  rw [← s_order]
  exact (SemiconjBy.orderOf_eq n (x := pS) (y := n * pS * n⁻¹) (by unfold SemiconjBy; group)).symm

theorem norm_le :
    Nat.card {x : j2P // x * pA * x⁻¹ ∈ KB ∧ x * pB * x⁻¹ ∈ KB} ≤ 720 := by
  classical
  let I3 := {x : j2P // x * pA = pA * x ∧ x * pB = pB * x ∧
    orderOf (x : Equiv.Perm (Fin 315)) = 2}
  let N := {x : j2P // x * pA * x⁻¹ ∈ KB ∧ x * pB * x⁻¹ ∈ KB}
  let D := j2P ⊓ centralizer ({pS} : Set (Equiv.Perm (Fin 315)))
  let yf : N → I3 := fun n => ⟨⟨n.1.1 * pS * n.1.1⁻¹,
    j2P.mul_mem (j2P.mul_mem n.1.2 s_mem) (j2P.inv_mem n.1.2)⟩, conj_s_mem n.1.2 n.2.1 n.2.2⟩
  let r : I3 → Equiv.Perm (Fin 315) := fun y =>
    if h : ∃ n : N, yf n = y then (Classical.choose h).1.1 else 1
  have hr : ∀ n : N, ∃ m : N, r (yf n) = m.1.1 ∧ yf m = yf n := by
    intro n
    have h : ∃ m : N, yf m = yf n := ⟨n, rfl⟩
    refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
    simp only [r, dif_pos h]
  have hD : ∀ n : N, (r (yf n))⁻¹ * n.1.1 ∈ D := by
    intro n
    obtain ⟨m, hm1, hm2⟩ := hr n
    have e : m.1.1 * pS * m.1.1⁻¹ = n.1.1 * pS * n.1.1⁻¹ :=
      congrArg (fun z : I3 => (z.1 : Equiv.Perm (Fin 315))) hm2
    rw [hm1]
    refine mem_inf.2 ⟨j2P.mul_mem (j2P.inv_mem m.1.2) n.1.2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc m.1.1⁻¹ * n.1.1 * pS = m.1.1⁻¹ * (n.1.1 * pS * n.1.1⁻¹) * n.1.1 := by group
      _ = m.1.1⁻¹ * (m.1.1 * pS * m.1.1⁻¹) * n.1.1 := by rw [e]
      _ = pS * (m.1.1⁻¹ * n.1.1) := by group
  let g : N → I3 × D := fun n => (yf n, ⟨(r (yf n))⁻¹ * n.1.1, hD n⟩)
  have hg : Function.Injective g := by
    intro n n' h
    have h1 : yf n = yf n' := congrArg Prod.fst h
    have h2 : (r (yf n))⁻¹ * n.1.1 = (r (yf n'))⁻¹ * n'.1.1 :=
      congrArg (fun z : I3 × D => (z.2 : Equiv.Perm (Fin 315))) h
    rw [h1] at h2
    exact Subtype.ext (Subtype.ext (mul_left_cancel h2))
  have h := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod, inv_card] at h
  have hD240 : Nat.card D = 240 := (j2_rows_spec.1 j2Row2B j2Row2B_mem).2.2.2.2
  rw [hD240] at h
  exact h

theorem enumsK' : EnumsSub 315 j2Kb (closure (tp 315 '' {x | x ∈ j2KbGens.toArray})) :=
  (enumOK_spec hn kb_enum).1

theorem normCount_eq : j2NormCount = 720 := by
  have pa : CFSG.Sporadic.SmallOddCore.permOK 315 j2KbA = true := by
    rw [x_tabs.1]
    exact permOK_unpack (xc (by norm_num)) (xp (by norm_num)).2.2
  have pb : CFSG.Sporadic.SmallOddCore.permOK 315 j2KbB = true := by
    rw [x_tabs.2.1]
    exact permOK_unpack (xc (by norm_num)) (xp (by norm_num)).2.2
  have hc := card_normCount hn j2Chain_valid.1 enumsK' (rep_tp pa) (rep_tp pb)
  rw [j2_normCount_levelTables, ← j2P_eq_original] at hc
  rw [← hc]
  exact le_antisymm norm_le norm_ge

theorem levelTables_j2 : levelTables j2Chain = Certificates.IvkCent.j2ChainTbls :=
  levelTables_eq j2ChainArrays (chainCheckFacts PairJ2.chain_check.1)

theorem card_cp {f : Table → Bool} {Q : Equiv.Perm (Fin 315) → Prop} [DecidablePred Q]
    (hfQ : ∀ T g, Rep 315 T g → (f T = true ↔ Q g)) :
    Nat.card {x : j2P // Q x} = countProducts 315 f Certificates.IvkCent.j2ChainTbls (idT 315) := by
  have hspec := countProducts_spec hfQ (forall₂_levelTables hn j2Chain) (Rep.idT hn)
  have hQ := j2Chain_valid.1
  rw [j2P_eq_original, ← levelTables_j2, hspec, card_subtype_eq_countP j2Chain.originalSubgroup
    (enumeration j2Chain) (enumeration_nodup j2Chain hQ) (mem_enumeration_iff j2Chain hQ) Q]
  simp only [one_mul, List.map_id']
  rfl

theorem repA' : Rep 315 j2KbA pA := by
  have h := repA
  rwa [← x_tabs.1] at h

theorem repB'' : Rep 315 j2KbB pB := by
  have h := repB
  rwa [← x_tabs.2.1] at h

theorem repU' : Rep 315 j2OuterTbl j2u := by
  have h := repU
  rwa [← tabF (by norm_num : 0 < 42), ← j2OuterTbl] at h

theorem innerCount_eq : Certificates.IvkCent.j2CentInnerCount = 12 := by
  unfold Certificates.IvkCent.j2CentInnerCount
  rw [← card_cp (Q := fun g => g * pA = pA * g ∧ g * pB = pB * g ∧ True) (fun T g hT => by
    rw [Certificates.IvkCent.centKbPred, Bool.and_eq_true, commTT_iff hT repA',
      commTT_iff hT repB'', and_true])]
  exact inner_card

theorem outer_card : Nat.card {x : j2P // x * j2u * pA = pA * (x * j2u) ∧
    x * j2u * pB = pB * (x * j2u) ∧ True} = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun y => ?_⟩
  obtain ⟨x, e1, e2, -⟩ := y
  obtain ⟨hU2, -, -, hmap, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hUi : j2u⁻¹ = j2u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hU2)
  obtain ⟨-, -, -, f1, -, f3, f4, -⟩ := facts
  have cV := xc (j := 2) (by norm_num)
  have hV2 : pV * pV = 1 := by
    rw [← pow_two, ← orderOf_eq_two_of_involOK hn repV (by rw [involF cV]; exact f1)]
    exact pow_orderOf_eq_one pV
  have hVt : pV * pT = pT * pV :=
    (commTT_iff repV repT).1 (by rw [commF cV (Fc (by norm_num))]; exact f4)
  have hVU : pV * j2u ∈ j2P := by
    have hr : Rep 315 (tabT (unpack 315 9 (pc (J2XT 2) (F 0)))) (pV * j2u) := by
      unfold pc
      rw [← compT_unpack cV (Fc (by norm_num))]
      exact Rep.compT repV repU
    exact (j2_groupData.sift _ _ hr).1 (by
      change j2Sift (tabT (unpack 315 9 (pcomp 315 9 (mask 9) (J2XT 2) (F 0)))) = true
      rw [sift_eq (CFSG.KC.BfsPin.canonK_pcomp cV (Fc (by norm_num)))]
      exact f3)
  set c := pH⁻¹ * (x.1 * j2u) * pH with hc
  have hct : c * pT = pT * c := (commA_iff _).1 e1
  have hcB : c * (pH⁻¹ * pB * pH) = pH⁻¹ * pB * pH * c := (commB_iff _).1 e2
  have hd : pV * c ∈ CT := by
    refine mem_CT.2 ⟨?_, ?_⟩
    · have e : pV * c = (pV * j2u) * (j2u * (pH⁻¹ * x.1) * j2u⁻¹) * pH := by
        rw [show j2u * (pH⁻¹ * x.1) * j2u⁻¹ = j2u⁻¹ * (pH⁻¹ * x.1) * j2u by rw [hUi], hc]
        group
      rw [e]
      exact j2P.mul_mem (j2P.mul_mem hVU (hUn _ (j2P.mul_mem (j2P.inv_mem pH_mem) x.2))) pH_mem
    · rw [mul_assoc, hct, ← mul_assoc, hVt, mul_assoc]
  obtain ⟨k, hk, hrk⟩ := enumsCT.2 _ hd
  rw [c2_get hk] at hrk
  have hk' : k < J2C2.cnt := by rw [c2_arr, hRec_size] at hk; exact hk
  have h := allN_spec c2_outer k hk'
  rw [pcomm2K_eq cV (c2c hk') cB, bIf_not] at h
  have hr : Rep 315 (tabT (unpack 315 9 (pc (J2XT 2) (J2C2.T k)))) c := by
    have e : c = pV * (pV * c) := by rw [← mul_assoc, hV2, one_mul]
    rw [e]
    unfold pc
    rw [← compT_unpack cV (c2c hk')]
    exact Rep.compT repV hrk
  have h2 := (commTT_iff hr repB').2 hcB
  unfold pc at h2
  rw [commF (CFSG.KC.BfsPin.canonK_pcomp cV (c2c hk')) cB] at h2
  have h3 : Nat.beq (pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (J2XT 2) (J2C2.T k)) bK)
      (pcomp 315 9 (mask 9) bK (pcomp 315 9 (mask 9) (J2XT 2) (J2C2.T k))) = true := h2
  rw [h3] at h
  exact Bool.noConfusion h

theorem outerCount_eq : Certificates.IvkCent.j2CentOuterCount = 0 := by
  unfold Certificates.IvkCent.j2CentOuterCount
  rw [← card_cp (Q := fun g => g * j2u * pA = pA * (g * j2u) ∧ g * j2u * pB = pB * (g * j2u) ∧ True)
    (fun T g hT => by
      rw [Certificates.IvkCent.centKbOuterPred, Certificates.IvkCent.centKbPred, Bool.and_eq_true,
        commTT_iff (Rep.compT hT repU') repA', commTT_iff (Rep.compT hT repU') repB'', and_true])]
  exact outer_card

end CertificateChecks.KernelGH74.J2Norm

end
