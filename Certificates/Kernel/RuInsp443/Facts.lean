module

public import Certificates.Kernel.RuInsp443.Checks
public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Certificates.Data.RuInsp443
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuInsp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.RuInsp CFSG.KC.BfsPin
  CFSG.Quasithin.KGC31.Ru CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuCe

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem g6A_5 : g6A[5]! = ruNs1A := rfl
theorem G6_5 : G6 5 = Ns1 := rfl
theorem G6I_5 : G6I 5 = Ns1I := rfl

theorem g6_at : ∀ j < 6, (g6A[j]! = ruA0A ∧ G6 j = A0 ∧ G6I j = A0I) ∨
    (g6A[j]! = ruA1A ∧ G6 j = A1 ∧ G6I j = A1I) ∨ (g6A[j]! = ruC0A ∧ G6 j = C0 ∧ G6I j = C0I) ∨
    (g6A[j]! = ruC1A ∧ G6 j = C1 ∧ G6I j = C1I) ∨
    (g6A[j]! = ruNs0A ∧ G6 j = Ns0 ∧ G6I j = Ns0I) ∨
    (g6A[j]! = ruNs1A ∧ G6 j = Ns1 ∧ G6I j = Ns1I) := by
  intro j hj
  interval_cases j
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g6A_5, G6_5, G6I_5⟩))))

theorem g6_binds : g6A.size = 6 ∧ ∀ j < 6, g6A[j]! = unpack 4060 12 (G6 j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rcases g6_at j hj with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ |
      ⟨e1, e2, -⟩ <;> rw [e1, e2]
  · exact a0_eq
  · exact a1_eq
  · exact c0_eq
  · exact c1_eq
  · exact ns0_eq
  · exact ns1_eq

theorem g6_perms :
    allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (G6 j) (G6I j)) = true := by
  refine PackFld.allN_of_forall fun j hj => ?_
  rcases g6_at j hj with ⟨-, e2, e3⟩ | ⟨-, e2, e3⟩ | ⟨-, e2, e3⟩ | ⟨-, e2, e3⟩ | ⟨-, e2, e3⟩ |
      ⟨-, e2, e3⟩ <;> rw [e2, e3]
  · exact pA0
  · exact pA1
  · exact pC0
  · exact pC1
  · exact pNs0
  · exact pNs1

theorem wA_eq {wd : List Int} {r : Nat} (h : wd6 wd r = true) : wA wd = unpack 4060 12 r :=
  (wordEqK_sound g6_binds g6_perms h).1

theorem cn_all : cn (XK 0) = true ∧ cn (XK 1) = true ∧ cn (XK 2) = true ∧ cn (KG 0) = true ∧
    cn (BV 0) = true ∧ cn (BV 1) = true ∧ cn (BV 2) = true ∧ cn (BV 3) = true ∧
    cn (BV 4) = true ∧ cn (BE 0) = true ∧ cn (BE 1) = true ∧ cn (BE 2) = true ∧
    cn (pidn 4060 12) = true := by
  have h := cAll
  simp only [bAnd_iff] at h
  exact h

theorem bv_eq : bV32EA = BVs.map (unpack 4060 12) := by
  change [wA (basisV32EW.getD 0 []), wA (basisV32EW.getD 1 []), wA (basisV32EW.getD 2 []),
    wA (basisV32EW.getD 3 []), wA (basisV32EW.getD 4 [])] = _
  rw [wA_eq bv0, wA_eq bv1, wA_eq bv2, wA_eq bv3, wA_eq bv4]
  rfl

theorem be_eq : bEA = BEs.map (unpack 4060 12) := by
  change [wA (basisEW.getD 0 []), wA (basisEW.getD 1 []), wA (basisEW.getD 2 [])] = _
  rw [wA_eq be0, wA_eq be1, wA_eq be2]
  rfl

theorem maskA_eq : ∀ (Ps : List Nat), (∀ p ∈ Ps, cn p = true) → ∀ k,
    maskA (Ps.map (unpack 4060 12)) k =
        unpack 4060 12 (maskL 4060 12 (mask 12) (pidn 4060 12) Ps k) ∧
      cn (maskL 4060 12 (mask 12) (pidn 4060 12) Ps k) = true
  | [], _, k => ⟨(idK_sound idOK).symm, cn_all.2.2.2.2.2.2.2.2.2.2.2.2⟩
  | b :: Ps, hP, k => by
    obtain ⟨ih1, ih2⟩ := maskA_eq Ps (fun p hp => hP p (List.mem_cons_of_mem b hp)) (k / 2)
    have hb := hP b List.mem_cons_self
    have hid := cn_all.2.2.2.2.2.2.2.2.2.2.2.2
    have e : maskL 4060 12 (mask 12) (pidn 4060 12) (b :: Ps) k =
        pcomp 4060 12 (mask 12) (nIf(Nat.beq (Nat.mod k 2) 1, b, pidn 4060 12))
          (maskL 4060 12 (mask 12) (pidn 4060 12) Ps (Nat.div k 2)) := rfl
    have hsel : (if k % 2 = 1 then unpack 4060 12 b else idA 4060) =
        unpack 4060 12 (nIf(Nat.beq (Nat.mod k 2) 1, b, pidn 4060 12)) ∧
          cn (nIf(Nat.beq (Nat.mod k 2) 1, b, pidn 4060 12)) = true := by
      by_cases hk : k % 2 = 1
      · have : Nat.beq (Nat.mod k 2) 1 = true := Nat.beq_eq_true_eq _ _ ▸ hk
        rw [if_pos hk, this]
        exact ⟨rfl, hb⟩
      · have : Nat.beq (Nat.mod k 2) 1 = false := by
          cases h : Nat.beq (Nat.mod k 2) 1
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) hk
        rw [if_neg hk, this]
        exact ⟨(idK_sound idOK).symm, hid⟩
    have e2 : maskA (List.map (unpack 4060 12) (b :: Ps)) k =
        compA 4060 (if k % 2 = 1 then unpack 4060 12 b else idA 4060)
          (maskA (Ps.map (unpack 4060 12)) (k / 2)) := rfl
    rw [e2, e, hsel.1, ih1]
    exact ⟨compA_unpack hsel.2 ih2, canonK_pcomp hsel.2 ih2⟩

theorem spanA_eq (Ps : List Nat) (hP : ∀ p ∈ Ps, cn p = true) :
    spanA (Ps.map (unpack 4060 12)) = (List.range (2 ^ Ps.length)).map fun k =>
      unpack 4060 12 (maskL 4060 12 (mask 12) (pidn 4060 12) Ps k) := by
  rw [spanA, List.length_map]
  exact List.map_congr_left fun k _ => (maskA_eq Ps hP k).1

theorem commA_unpack {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    commA (unpack 4060 12 p) (unpack 4060 12 q) =
      Nat.beq (pcomp 4060 12 (mask 12) p q) (pcomp 4060 12 (mask 12) q p) := by
  rw [commA, compA_unpack hp hq, compA_unpack hq hp,
    eqA_unpack (canonK_pcomp hp hq) (canonK_pcomp hq hp)]
  cases he : Nat.beq (pcomp 4060 12 (mask 12) p q) (pcomp 4060 12 (mask 12) q p)
  · exact Bool.and_false _
  · rw [Bool.and_true, List.all_eq_true]
    intro i hi
    have hi' : i < 4060 := by have := List.mem_range.1 hi; omega
    have e : (compA 4060 (unpack 4060 12 p) (unpack 4060 12 q))[i]! =
        (compA 4060 (unpack 4060 12 q) (unpack 4060 12 p))[i]! := by
      rw [compA_unpack hp hq, compA_unpack hq hp, Nat.eq_of_beq_eq_true he]
    rw [compA_get hi', compA_get hi'] at e
    rw [e, beq_self_eq_true]

theorem cK_eq : commutA ruKGensA[0]! xEA = unpack 4060 12 CK := by
  obtain ⟨c0, c1, c2, cK, -⟩ := cn_all
  have hk : ruKGensA[0]! = unpack 4060 12 (KG 0) := kg_eq (by norm_num)
  have hx : xEA = unpack 4060 12 (XK 0) := wA_eq xW
  have hki : ruInv ruKGensA[0]! = unpack 4060 12 (XK 2) := by
    rw [ruInv, hk]
    exact (invEqK_sound pK).1
  have hxi : ruInv xEA = unpack 4060 12 (XK 1) := by
    rw [ruInv, hx]
    exact (invEqK_sound pX).1
  rw [commutA, hki, hxi, hk, hx, compA_unpack cK c0, compA_unpack (canonK_pcomp cK c0) c2,
    compA_unpack (canonK_pcomp (canonK_pcomp cK c0) c2) c1]
  rfl

theorem cn_CK : cn CK = true := by
  obtain ⟨c0, c1, c2, cK, -⟩ := cn_all
  exact canonK_pcomp (canonK_pcomp (canonK_pcomp cK c0) c2) c1

theorem cn_BVs : ∀ p ∈ BVs, cn p = true := by
  obtain ⟨-, -, -, -, h0, h1, h2, h3, h4, -⟩ := cn_all
  intro p hp
  simp only [BVs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem cn_BEs : ∀ p ∈ BEs, cn p = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0, h1, h2, -⟩ := cn_all
  intro p hp
  simp only [BEs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> assumption

theorem chkKxE_true : chkKxE () = true := by
  have hchk := chk
  unfold chkKxEK at hchk
  have hall := allN_spec hchk
  rw [chkKxE, cK_eq, spV32E, spE, bv_eq, be_eq, spanA_eq BVs cn_BVs, spanA_eq BEs cn_BEs]
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
  have hk' : k < 2 ^ 5 := List.mem_range.1 hk
  have hvk := (maskA_eq BVs cn_BVs k).2
  have h := hall k hk'
  rw [strictB_eq'] at h
  rw [commA_unpack hvk cn_CK]
  cases hc : Nat.beq (pcomp 4060 12 (mask 12) (maskL 4060 12 (mask 12) (pidn 4060 12) BVs k) CK)
      (pcomp 4060 12 (mask 12) CK (maskL 4060 12 (mask 12) (pidn 4060 12) BVs k))
  · rfl
  · rw [hc] at h
    change bIf(allN (Nat.pow 2 3) _, false, true) = true at h
    cases ha : allN (Nat.pow 2 3) (fun j => bIf(Nat.beq (maskL 4060 12 (mask 12) (pidn 4060 12)
        BEs j) (maskL 4060 12 (mask 12) (pidn 4060 12) BVs k), false, true))
    · rw [Bool.not_true, Bool.false_or, inA, List.any_eq_true]
      have : ∃ j < 2 ^ 3, Nat.beq (maskL 4060 12 (mask 12) (pidn 4060 12) BEs j)
          (maskL 4060 12 (mask 12) (pidn 4060 12) BVs k) = true := by
        by_contra hne
        push Not at hne
        have : allN (Nat.pow 2 3) (fun j => bIf(Nat.beq (maskL 4060 12 (mask 12) (pidn 4060 12)
            BEs j) (maskL 4060 12 (mask 12) (pidn 4060 12) BVs k), false, true)) = true :=
          PackFld.allN_of_forall fun j hj => by
            have := hne j hj
            simp only [ne_eq, Bool.not_eq_true] at this
            rw [this]
        rw [this] at ha
        exact Bool.false_ne_true ha.symm
      obtain ⟨j, hj, he⟩ := this
      have hj' : j < 2 ^ BEs.length := hj
      refine ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj', rfl⟩, ?_⟩
      rw [eqA_unpack (maskA_eq BEs cn_BEs j).2 hvk]
      exact he
    · rw [ha] at h
      exact absurd h Bool.false_ne_true

end CertificateChecks.KernelRuInsp

end
