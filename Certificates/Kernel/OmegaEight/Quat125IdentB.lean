module

public import Certificates.Kernel.OmegaEight.Quat125Ident
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckC
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.O8QuatSound
public import Certificates.Kernel.OmegaEight.Roots127Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4.E4C

@[expose] noncomputable def q125Q (Y R V : Nat) : List Nat :=
  [idK, Y, R, matMulK R Y, V, matMulK V Y, matMulK R V, matMulK (matMulK R V) Y]

theorem q125_notb {c : Bool} (h : Bool.rec (motive := fun _ => Bool) true false c = true) :
    c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

theorem q125_memK_f {x : Nat} : ∀ {L : List Nat}, memK x L = false → x ∉ L
  | [], _, hx => absurd hx List.not_mem_nil
  | a :: L, h, hx => by
    change bIf(Nat.beq a x, true, memK x L) = false at h
    cases e : Nat.beq a x
    · rw [e] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [Nat.beq_refl] at e
        exact absurd e (by decide)
      · exact q125_memK_f h hx
    · rw [e] at h
      have h' : true = false := h
      exact absurd h' (by decide)

theorem q125_witK {R V C D e a b : Nat} {Q : List Nat} (h : witK R V Q C D e a b = true) :
    (matMulK (matMulK C R) D ∉ Q ∨ matMulK (matMulK C V) D ∉ Q) ∧
      ∃ X ∈ [R, V], ∃ Z ∈ [matMulK (matMulK C R) D, matMulK (matMulK C V) D],
        matMulK X Z ≠ matMulK Z X := by
  unfold witK at h
  simp only [q125sB] at h
  obtain ⟨h1, h2⟩ := q125bAnd.1 h
  have m := q125_memK_f (q125_notb h1)
  have n := Nat.ne_of_beq_eq_false (q125_notb h2)
  refine ⟨?_, _, ?_, _, ?_, n⟩
  · cases he : Nat.beq e 0 <;> rw [he] at m
    · exact Or.inr m
    · exact Or.inl m
  · cases Nat.beq a 0
    · change V ∈ [R, V]
      simp
    · change R ∈ [R, V]
      simp
  · cases Nat.beq b 0
    · change matMulK (matMulK C V) D ∈ [matMulK (matMulK C R) D, matMulK (matMulK C V) D]
      simp
    · change matMulK (matMulK C R) D ∈ [matMulK (matMulK C R) D, matMulK (matMulK C V) D]
      simp

theorem q125_tagOK {SC : Nat} {Ls : List (List Nat)} {C0 D0 C1 D1 C2 D2 k Y R V tag : Nat}
    (h : tagOK SC Ls C0 D0 C1 D1 C2 D2 k Y R V tag = true) :
    (k = 10 ∧ Nat.div tag 4 < 4 ∧ subK (q125Q Y R V) (listAtK SC Ls (Nat.div tag 4)) = true) ∨
    ∃ C D, ((k = 10 ∧ (C = C0 ∧ D = D0 ∨ C = C1 ∧ D = D1)) ∨ (k = 37 ∧ C = C2 ∧ D = D2)) ∧
      ∃ e a b, witK R V (q125Q Y R V) C D e a b = true := by
  unfold tagOK at h
  simp only [q125sB] at h
  by_cases hm : Nat.mod tag 4 = 0
  · rw [q125bIfT (q125beqT hm)] at h
    obtain ⟨h1, h23⟩ := q125bAnd.1 h
    obtain ⟨h2, h3⟩ := q125bAnd.1 h23
    have := q125blt.1 h2
    refine Or.inl ⟨Nat.eq_of_beq_eq_true h1, ?_, h3⟩
    change tag / 4 < 4
    omega
  · rw [q125bIfF (q125beqF hm)] at h
    obtain ⟨-, h23⟩ := q125bAnd.1 h
    obtain ⟨h2, h3⟩ := q125bAnd.1 h23
    right
    set w := Nat.land (Nat.sub tag 1) 7
    refine ⟨_, _, ?_, _, _, _, h3⟩
    cases hk : Nat.beq k 10
    · rw [hk] at h2
      obtain ⟨a1, a2⟩ := q125bAnd.1 h2
      rw [Nat.eq_of_beq_eq_true a2]
      exact Or.inr ⟨Nat.eq_of_beq_eq_true a1, rfl, rfl⟩
    · rw [hk] at h2
      have hw := q125blt.1 h2
      refine Or.inl ⟨Nat.eq_of_beq_eq_true hk, ?_⟩
      rcases (by omega : w = 0 ∨ w = 1) with e | e
      · rw [e]
        exact Or.inl ⟨rfl, rfl⟩
      · rw [e]
        exact Or.inr ⟨rfl, rfl⟩

section Ident


theorem q125_saAt_lt (i : Nat) : saAtK saCodes i < 2 ^ 64 := by
  rw [q125_saAt]
  exact saMat_lt i

theorem q125_acts_elt {i : Nat} (hi : i < 8192) : Acts (saElt i) (saAtK saCodes i) := by
  rw [q125_saAt]
  exact (saElt_spec sa_facts i hi).2

theorem q125_q8_acts {y ρ j : Equiv.Perm (Fin 360)} {Y R V : Nat} (aY : Acts y Y) (aR : Acts ρ R)
    (aV : Acts j V) (bY : Y < 2 ^ 64) (bR : R < 2 ^ 64) (bV : V < 2 ^ 64) :
    ∀ q ∈ q8Elems y ρ j, ∃ M ∈ q125Q Y R V, M < 2 ^ 64 ∧ Acts q M := by
  intro q hq
  simp only [q8Elems, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨idK, by simp [q125Q], ?_, ?_⟩
    · rw [CertificateChecks.KernelO8.idK_eq]
      exact idCode_lt
    · rw [CertificateChecks.KernelO8.idK_eq]
      exact acts_one
  · exact ⟨Y, by simp [q125Q], bY, aY⟩
  · exact ⟨R, by simp [q125Q], bR, aR⟩
  · exact ⟨_, by simp [q125Q], q125_mm_lt _ _, q125_acts_mul aR aY⟩
  · exact ⟨V, by simp [q125Q], bV, aV⟩
  · exact ⟨_, by simp [q125Q], q125_mm_lt _ _, q125_acts_mul aV aY⟩
  · exact ⟨_, by simp [q125Q], q125_mm_lt _ _, q125_acts_mul aR aV⟩
  · exact ⟨_, by simp [q125Q], q125_mm_lt _ _, q125_acts_mul (q125_acts_mul aR aV) aY⟩

theorem q125_twin_contra {K : Subgroup (Equiv.Perm (Fin 360))} {y ρ j c : Equiv.Perm (Fin 360)}
    {Y R V C D : Nat} (hd : Vtx.AmbientQuatDatum omegaT K y) (hK : ∀ x, x ∈ K ↔ x ∈ q8Elems y ρ j)
    (aY : Acts y Y) (aR : Acts ρ R) (aV : Acts j V) (bY : Y < 2 ^ 64) (bR : R < 2 ^ 64)
    (bV : V < 2 ^ 64) (hc : c ∈ omegaT) (hcy : c * y = y * c) (aC : Acts c C) (aD : Acts c⁻¹ D)
    (h1 : matMulK (matMulK C R) D ∉ q125Q Y R V ∨ matMulK (matMulK C V) D ∉ q125Q Y R V)
    (h2 : ∃ X ∈ [R, V], ∃ Z ∈ [matMulK (matMulK C R) D, matMulK (matMulK C V) D],
      matMulK X Z ≠ matMulK Z X) : False := by
  have hq := q125_q8_acts aY aR aV bY bR bV
  have hρK : ρ ∈ K := (hK ρ).2 (by simp [q8Elems])
  have hjK : j ∈ K := (hK j).2 (by simp [q8Elems])
  have acr : Acts (c * ρ * c⁻¹) (matMulK (matMulK C R) D) :=
    q125_acts_mul (q125_acts_mul aC aR) aD
  have acv : Acts (c * j * c⁻¹) (matMulK (matMulK C V) D) :=
    q125_acts_mul (q125_acts_mul aC aV) aD
  rcases hd.twins c hc hcy with heq | hcomm
  · have key : ∀ x ∈ K, ∀ X, Acts (c * x * c⁻¹) X → X < 2 ^ 64 → X ∉ q125Q Y R V → False := by
      intro x hx X aX bX hX
      have hm : c * x * c⁻¹ ∈ K := by
        rw [← heq]
        exact conj_mem_conjSub hx
      obtain ⟨M, hM, bM, aM⟩ := hq _ ((hK _).1 hm)
      exact hX (by rw [acts_unique sa_facts bX bM aX aM]; exact hM)
    rcases h1 with h1 | h1
    · exact key ρ hρK _ acr (q125_mm_lt _ _) h1
    · exact key j hjK _ acv (q125_mm_lt _ _) h1
  · obtain ⟨X, hX, Z, hZ, hne⟩ := h2
    obtain ⟨x, hxK, aX⟩ : ∃ x ∈ K, Acts x X := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact ⟨ρ, hρK, aR⟩
      · exact ⟨j, hjK, aV⟩
    obtain ⟨z, hzK, aZ⟩ : ∃ z ∈ conjSub c K, Acts z Z := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
      rcases hZ with rfl | rfl
      · exact ⟨_, conj_mem_conjSub hρK, acr⟩
      · exact ⟨_, conj_mem_conjSub hjK, acv⟩
    have e := hcomm x hxK z hzK
    have a1 := q125_acts_mul aX aZ
    have a2 := q125_acts_mul aZ aX
    rw [e] at a1
    exact hne (acts_unique sa_facts (q125_mm_lt _ _) (q125_mm_lt _ _) a1 a2)

theorem q125_wit01 {w : Nat} (hw : w < 2) : ∃ c ∈ omegaT, c * repPerm 10 = repPerm 10 * c ∧
    Acts c (r127M (wO (q125WW.getD w []))) ∧ Acts c⁻¹ (r127M (pinv (wO (q125WW.getD w [])))) := by
  have hp : q125WW.getD w [] ∈ q125WW := by
    rw [List.getD_eq_getElem _ _ (by change w < 2; exact hw)]
    exact List.getElem_mem _
  have hW := kWit125
  simp only [q125bAnd] at hW
  have hwit := List.all_eq_true.1 hW.1 _ hp
  beta_reduce at hwit
  obtain ⟨hlet, hwit⟩ := q125bAnd.1 hwit
  rw [q125sB] at hwit
  beta_reduce at hwit
  rw [q125sB] at hwit
  beta_reduce at hwit
  obtain ⟨hcn, hwit⟩ := q125bAnd.1 hwit
  obtain ⟨hpm, hwit⟩ := q125bAnd.1 hwit
  obtain ⟨hcni, hwit⟩ := q125bAnd.1 hwit
  obtain ⟨hcomm, hwit⟩ := q125bAnd.1 hwit
  obtain ⟨hac, hwit⟩ := q125bAnd.1 hwit
  obtain ⟨haci, -⟩ := q125bAnd.1 hwit
  have hlo : lettersOK 17 (q125WW.getD w []) = true := by
    rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl <;> decide +kernel
  obtain ⟨hcr, hcm⟩ := omegaW_spec hlo
  obtain ⟨c, hcdef⟩ : ∃ c, c = permOfArr 360 (omegaW (q125WW.getD w [])) := ⟨_, rfl⟩
  rw [← hcdef] at hcr hcm
  rw [omegaW_eq hlet] at hcr
  have hci : Rep 360 (unpack 360 9 (pinv (wO (q125WW.getD w [])))) c⁻¹ := by
    rw [← invCand_pinv hpm]
    exact rep_inv_of_isInvA hcr (isInvA_of hpm)
  have hm := (main_ok (i := 0) (by norm_num)).2.1
  refine ⟨c, hcm, ?_, acts_of_rep hcr (acts_of hac), acts_of_rep hci (acts_of haci)⟩
  rw [← q125_main0]
  have r1 := q125_rep_pc hcn hm hcr (q125_rep_main (t := 0) (by norm_num))
  rw [Nat.eq_of_beq_eq_true hcomm] at r1
  exact r1.unique (q125_rep_pc hm hcn (q125_rep_main (t := 0) (by norm_num)) hcr)

theorem q125_wit37 : ∃ c ∈ omegaT, c * repPerm 37 = repPerm 37 * c ∧
    Acts c (saAtK saCodes wit37) ∧ Acts c⁻¹ (saAtK saCodes wit37i) := by
  have h := kWit125
  simp only [q125bAnd] at h
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  rw [q125sB] at h5
  beta_reduce at h5
  have hw := q125blt.1 h1
  have hwi := q125blt.1 h2
  have aY : Acts (repPerm 37) (saAtK saCodes (ix13 yIdxT 37)) := by
    have hY := kY127
    rw [q125sB] at hY
    rw [← Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec hY 37 (by norm_num))]
    exact q125_acts_rep (by norm_num)
  have aC := q125_acts_elt hw
  have aCi := q125_acts_elt hwi
  have hS := (saElt_spec sa_facts _ hw).1
  have hSi := (saElt_spec sa_facts _ hwi).1
  have hYS := (repPerm_spec (j := 37) (by norm_num)).2
  have hone : saElt wit37 * saElt wit37i = 1 := by
    have a := q125_acts_mul aC aCi
    rw [Nat.eq_of_beq_eq_true h4, CertificateChecks.KernelO8.idK_eq] at a
    exact eq_of_acts sa_facts (sylowT.mul_mem hS hSi) sylowT.one_mem idCode_lt a acts_one
  have hinv : saElt wit37i = (saElt wit37)⁻¹ := eq_inv_of_mul_eq_one_right hone
  refine ⟨saElt wit37, (parK_spec _ hw).2 (Nat.eq_of_beq_eq_true h3), ?_, aC, hinv ▸ aCi⟩
  have a1 := q125_acts_mul aC aY
  have a2 := q125_acts_mul aY aC
  rw [Nat.eq_of_beq_eq_true h5] at a1
  exact eq_of_acts sa_facts (sylowT.mul_mem hS hYS) (sylowT.mul_mem hYS hS) (q125_mm_lt _ _) a1 a2

theorem q125_lists {j : Nat} (hj : j < 4) : (lists.getD j []).length = 8 ∧
    ∀ a ∈ lists.getD j [], a < 8192 := by
  have h := kLists125
  simp only [q125bAnd] at h
  have h' := CFSG.KC.Pack.allN_spec h.2.2.1 j hj
  obtain ⟨hl, ha⟩ := q125bAnd.1 h'
  have hl' : (lists.getD j []).length = 8 := Nat.eq_of_beq_eq_true hl
  refine ⟨hl', fun a hmem => ?_⟩
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hmem
  have hb := CFSG.KC.Pack.allN_spec ha n (by rw [← hl']; exact hn)
  rw [q125sB] at hb
  change bAnd(Nat.blt ((lists.getD j []).getD n 0) 8192, _) = true at hb
  rw [List.getD_eq_getElem _ _ hn] at hb
  exact q125blt.1 (q125bAnd.1 hb).1

theorem q125_classify {k : Nat} (hk : k < 38) (ht : q125Ty k = 1)
    {K : Subgroup (Equiv.Perm (Fin 360))} (hd : Vtx.AmbientQuatDatum omegaT K (repPerm k))
    (hKS : K ≤ sylowT) :
    k = 10 ∧ ∃ γ ∈ omegaT, ∃ j < 4, ∀ x, x ∈ conjSub γ K ↔ x ∈ (lists.getD j []).map saElt := by
  classical
  set y := repPerm k with hy
  have aY : Acts y (saAtK (ycK saCodes yIdxT) k) := q125_acts_rep hk
  have bY : saAtK (ycK saCodes yIdxT) k < 2 ^ 64 := q125_YP_lt k
  have hyS : y ∈ sylowT := (repPerm_spec hk).2
  have hy2 : y * y = 1 := by rw [← pow_two, ← orderOf_repPerm hk, pow_orderOf_eq_one]
  obtain ⟨e⟩ := hd.q8
  set ρ : Equiv.Perm (Fin 360) := ((e.symm (QuaternionGroup.a 1) : K) : Equiv.Perm (Fin 360))
    with hρ
  have hρK : ρ ∈ K := (e.symm (QuaternionGroup.a 1)).2
  have hρ4 : orderOf ρ = 4 := by
    rw [hρ, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  have hρne : ρ * ρ ≠ 1 := fun h1 => by
    have h2 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
    rw [hρ4] at h2
    norm_num at h2
  have hρr : ρ * ρ = y := by
    have h4 : ρ ^ 4 = 1 := hρ4 ▸ pow_orderOf_eq_one ρ
    have hsq : ρ * ρ * (ρ * ρ) = 1 := by
      rw [← h4]
      simp [pow_succ, mul_assoc]
    exact (hd.inv.unique _ (K.mul_mem hρK hρK) hsq).resolve_left hρne
  obtain ⟨i₁, hi₁, hρe⟩ := exists_saElt sa_facts (hKS hρK)
  have hp₁ : parK saParT saLabT i₁ = 0 := (parK_spec i₁ hi₁).1 (by rw [hρe]; exact hd.le hρK)
  have aρ : Acts ρ (saAtK saCodes i₁) := by
    rw [← hρe]
    exact q125_acts_elt hi₁
  have hs₁ : matMulK (saAtK saCodes i₁) (saAtK saCodes i₁) = saAtK (ycK saCodes yIdxT) k := by
    have a := q125_acts_mul aρ aρ
    rw [hρr] at a
    exact acts_unique sa_facts (q125_mm_lt _ _) bY a aY
  obtain ⟨e₁, he₁, hei, hek⟩ := q125_exists_entry hi₁ hp₁ (by rw [hs₁]; exact q125_look hk ht)
  obtain ⟨⟨e', he', he'i, he'r⟩, hc8, hcp, hcI, hcY⟩ := q125_class he₁
  rw [hei] at hcI
  rw [hek] at hcY
  set r := e₁.2.2.1
  set c := e₁.2.2.2.1
  have hr8 : r < 8192 := by
    rw [← he'i]
    exact (q125_entry he').1
  set γ := saElt c
  have hγS : γ ∈ sylowT := (saElt_spec sa_facts c hc8).1
  have hγΩ : γ ∈ omegaT := (parK_spec c hc8).2 hcp
  have aγ : Acts γ (saAtK saCodes c) := q125_acts_elt hc8
  have hγy : γ * y = y * γ := by
    have a1 := q125_acts_mul aγ aY
    have a2 := q125_acts_mul aY aγ
    rw [hcY] at a1
    exact eq_of_acts sa_facts (sylowT.mul_mem hγS hyS) (sylowT.mul_mem hyS hγS) (q125_mm_lt _ _) a1 a2
  set ρ' := saElt r
  have hρ'S : ρ' ∈ sylowT := (saElt_spec sa_facts r hr8).1
  have aρ' : Acts ρ' (saAtK saCodes r) := q125_acts_elt hr8
  have hγρ : γ * ρ = ρ' * γ := by
    have a1 := q125_acts_mul aγ aρ
    have a2 := q125_acts_mul aρ' aγ
    rw [hcI] at a1
    exact eq_of_acts sa_facts (sylowT.mul_mem hγS (hKS hρK)) (sylowT.mul_mem hρ'S hγS)
      (q125_mm_lt _ _) a1 a2
  have hρ'e : ρ' = γ * ρ * γ⁻¹ := by rw [hγρ]; group
  have hγyγ : γ * y * γ⁻¹ = y := by rw [hγy]; group
  have hd'' : Vtx.AmbientQuatDatum omegaT (conjSub γ K) y := by
    have h1 := hd.conj hγΩ
    rwa [hγyγ] at h1
  have hK''S : conjSub γ K ≤ sylowT := fun x hx => by
    rw [mem_conjSub_iff] at hx
    rw [show x = γ * (γ⁻¹ * x * γ) * γ⁻¹ by group]
    exact sylowT.mul_mem (sylowT.mul_mem hγS (hKS hx)) (sylowT.inv_mem hγS)
  have hρ'K : ρ' ∈ conjSub γ K := by
    rw [hρ'e]
    exact conj_mem_conjSub hρK
  have hρ'r : ρ' * ρ' = y := by
    rw [hρ'e]
    calc γ * ρ * γ⁻¹ * (γ * ρ * γ⁻¹) = γ * (ρ * ρ) * γ⁻¹ := by group
      _ = y := by rw [hρr, hγyγ]
  obtain ⟨e''⟩ := hd''.q8
  have hρ'2 : ρ' * ρ' ≠ 1 := by
    rw [hρ'r]
    exact hd''.inv.ne_one
  obtain ⟨j₂, hj₂K, hjj, hjρ, hKT⟩ := exists_q8_gen e'' hρ'K hρ'2
  rw [hρ'r] at hjj hKT
  obtain ⟨v, hv, hje⟩ := exists_saElt sa_facts (hK''S hj₂K)
  have hvp : parK saParT saLabT v = 0 := (parK_spec v hv).1 (by rw [hje]; exact hd''.le hj₂K)
  have aj : Acts j₂ (saAtK saCodes v) := by
    rw [← hje]
    exact q125_acts_elt hv
  have hvs : matMulK (saAtK saCodes v) (saAtK saCodes v) = saAtK (ycK saCodes yIdxT) k := by
    have a := q125_acts_mul aj aj
    rw [hjj] at a
    exact acts_unique sa_facts (q125_mm_lt _ _) bY a aY
  have hrs : matMulK (saAtK saCodes r) (saAtK saCodes r) = saAtK (ycK saCodes yIdxT) k := by
    have a := q125_acts_mul aρ' aρ'
    rw [hρ'r] at a
    exact acts_unique sa_facts (q125_mm_lt _ _) bY a aY
  have hρ'inv : ρ'⁻¹ = ρ' * y := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hρ'r, hy2])
  have hanti : antiQK (saAtK saCodes r) (matMulK (saAtK saCodes r) (saAtK (ycK saCodes yIdxT) k))
      (saAtK saCodes v) = true := by
    have e1 : j₂ * ρ' = ρ' * y * j₂ := by
      rw [← hρ'inv, ← hjρ]
      group
    have a1 := q125_acts_mul aj aρ'
    have a2 := q125_acts_mul (q125_acts_mul aρ' aY) aj
    rw [e1] at a1
    exact q125beqT (acts_unique sa_facts (q125_mm_lt _ _) (q125_mm_lt _ _) a1 a2)
  have hrk : e'.2.1 = k := by
    have h1 := (q125_entry he').2.2
    have h2 := q125_look hk ht
    rw [he'i, hrs, h2] at h1
    omega
  have hpl := q125_pairs_at he' he'r
  rw [hrk, he'i] at hpl
  obtain ⟨tag, -, htag⟩ := q125_partner hk ht hpl hv hvp hvs hanti
  have bR := q125_saAt_lt r
  have bV := q125_saAt_lt v
  rcases q125_tagOK htag with ⟨hk10, hj4, hsub⟩ | ⟨C, D, hCD, ea, eb, ec, hwit⟩
  ·
    refine ⟨hk10, γ, hγΩ, _, hj4, ?_⟩
    obtain ⟨hlen, hlt⟩ := q125_lists hj4
    set L := (lists.getD (Nat.div tag 4) []).map saElt
    have hsubset : ∀ x ∈ conjSub γ K, x ∈ L := by
      intro x hx
      obtain ⟨M, hM, bM, aM⟩ := q125_q8_acts aY aρ' aj bY bR bV x ((hKT x).1 hx)
      have hML := q125_subK hsub M hM
      rw [q125_listAtK, q125_codesK] at hML
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hML
      have ha8 := hlt a ha
      have hxa := eq_of_acts sa_facts (hK''S hx) (saElt_spec sa_facts a ha8).1 bM aM
        (q125_acts_elt ha8)
      exact List.mem_map.2 ⟨a, ha, hxa.symm⟩
    have hcard : Nat.card (conjSub γ K) = 8 := by
      rw [Vtx.natCard_conjSub, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        QuaternionGroup.card]
    set F := L.toFinset.filter (· ∈ conjSub γ K)
    have hF : ∀ x, x ∈ F ↔ x ∈ conjSub γ K := fun x => by
      simp only [F, Finset.mem_filter, List.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsubset x h, h⟩⟩
    have hFc : F.card = 8 := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype F hF).symm
    have hLc : L.toFinset.card ≤ 8 := by
      refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map, hlen]
    have heq : F = L.toFinset := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hFc]; exact hLc)
    intro x
    refine ⟨hsubset x, fun hx => ?_⟩
    rw [← List.mem_toFinset, ← heq] at hx
    exact (hF x).1 hx
  ·
    exfalso
    obtain ⟨h1, h2⟩ := q125_witK hwit
    have key : ∀ c₀ ∈ omegaT, c₀ * y = y * c₀ → Acts c₀ C → Acts c₀⁻¹ D → False :=
      fun c₀ hc₀ hc₀y aC aD =>
        q125_twin_contra hd'' hKT aY aρ' aj bY bR bV hc₀ hc₀y aC aD h1 h2
    rcases hCD with ⟨hk10, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨hk37, rfl, rfl⟩
    · obtain ⟨c₀, h0, h0y, a0, a0'⟩ := q125_wit01 (w := 0) (by norm_num)
      rw [← hk10] at h0y
      exact key c₀ h0 h0y a0 a0'
    · obtain ⟨c₀, h0, h0y, a0, a0'⟩ := q125_wit01 (w := 1) (by norm_num)
      rw [← hk10] at h0y
      exact key c₀ h0 h0y a0 a0'
    · obtain ⟨c₀, h0, h0y, a0, a0'⟩ := q125_wit37
      rw [← hk37] at h0y
      exact key c₀ h0 h0y a0 a0'

theorem q125_ident0 {K : Subgroup (Equiv.Perm (Fin 360))}
    (hd : Vtx.AmbientQuatDatum omegaT K (mainPerm 0)) :
    ∃ γ ∈ omegaT, ∃ j < 4, ∀ x, x ∈ conjSub γ K ↔ x ∈ (lists.getD j []).map saElt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK : sylowT ≤ Subgroup.centralizer {mainPerm 0} := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (cent127 s hs)
  have hKS : K ≤ sylowT := by
    refine (CFSG.KC.O8Quat.le_of_twins (S := sylowT ⊓ omegaT) hd ?_ ?_ ?_).trans inf_le_left
    · intro x hx
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨h2, hSK h1⟩
    · exact (IsPGroup.of_card (n := 13) (by rw [card_sylowT]; norm_num)).to_le inf_le_left
    · intro Q hSQ hQp hQle
      obtain ⟨a, ⟨-, haA⟩, hconj⟩ := exists_conj_sylowT hSK (Q := Q)
        (fun q hq => ⟨(Subgroup.mem_inf.1 (hQle hq)).2,
          omegaT_le_autT (Subgroup.mem_inf.1 (hQle hq)).1⟩) hQp
      have hmap : Q.map (MulAut.conj a).toMonoidHom ≤ sylowT ⊓ omegaT := by
        rintro _ ⟨q, hq, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_inf.2 ⟨hconj q hq,
          (conj_mem_omegaT haA).1 (Subgroup.mem_inf.1 (hQle hq)).1⟩
      calc Nat.card Q = Nat.card (Q.map (MulAut.conj a).toMonoidHom) :=
            (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm
        _ ≤ _ := Subgroup.card_le_of_le hmap
  rw [q125_main0] at hd
  exact (q125_classify (by norm_num) rfl hd hKS).2

theorem q125_ident12 {i : Nat} (hi : i = 1 ∨ i = 2) {K : Subgroup (Equiv.Perm (Fin 360))}
    (hd : Vtx.AmbientQuatDatum omegaT K (mainPerm i)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ⟨-, haA⟩, hconj⟩ := exists_conj_sylowT (K := ⊤) le_top (Q := K)
    (fun q hq => ⟨Subgroup.mem_top q, omegaT_le_autT (hd.le hq)⟩)
    (CFSG.KC.O8Quat.datum_isPGroup hd)
  have hd1 := CFSG.KC.O8Quat.datum_conj_of_normalizes hd (fun _ => conj_mem_omegaT haA)
  have hK1 : conjSub a K ≤ sylowT := fun x hx => by
    rw [mem_conjSub_iff] at hx
    have h1 := hconj _ hx
    rwa [show a * (a⁻¹ * x * a) * a⁻¹ = x by group] at h1
  have hxS : a * mainPerm i * a⁻¹ ∈ sylowT := hK1 hd1.inv.mem
  have hxo : orderOf (a * mainPerm i * a⁻¹) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hd1.inv.sq) hd1.inv.ne_one
  obtain ⟨k, hk, c, hc, hce⟩ := exists_rep_of_involution hxS hxo
  have hcA : c ∈ autT := sylowT_le_autT hc
  have hd2 := CFSG.KC.O8Quat.datum_conj_of_normalizes hd1 (g := c⁻¹)
    (fun _ => conj_mem_omegaT (autT.inv_mem hcA))
  rw [hce, show c⁻¹ * (c * repPerm k * c⁻¹) * c⁻¹⁻¹ = repPerm k by group] at hd2
  have hK2 : conjSub c⁻¹ (conjSub a K) ≤ sylowT := fun x hx => by
    rw [mem_conjSub_iff] at hx
    rw [show x = c⁻¹ * (c⁻¹⁻¹ * x * c⁻¹) * c⁻¹⁻¹ by group]
    exact sylowT.mul_mem (sylowT.mul_mem (sylowT.inv_mem hc) (hK1 hx)) (sylowT.inv_mem
      (sylowT.inv_mem hc))
  have hty : repTypes.getD k 0 = i := by
    refine type127 _ (repTypes_lt hk) i (by omega) ((conjPerm k)⁻¹ * (c⁻¹ * a)) ?_
    have e := conj_mainPerm hk
    calc (conjPerm k)⁻¹ * (c⁻¹ * a) * mainPerm i * ((conjPerm k)⁻¹ * (c⁻¹ * a))⁻¹ =
          (conjPerm k)⁻¹ * (c⁻¹ * (a * mainPerm i * a⁻¹) * c) * conjPerm k := by group
      _ = (conjPerm k)⁻¹ * repPerm k * conjPerm k := by rw [hce]; group
      _ = mainPerm (repTypes.getD k 0) := by rw [← e]; group
  have ht : q125Ty k = 1 := by
    unfold q125Ty
    rw [q125sN]
    change nIf(Nat.beq k 10, 1, nIf(Nat.beq (repTypes.getD k 0) 1, 1,
      nIf(Nat.beq (repTypes.getD k 0) 2, 1, 0))) = 1
    rw [hty]
    cases Nat.beq k 10 <;> rcases hi with rfl | rfl <;> rfl
  obtain ⟨hk10, -⟩ := q125_classify hk ht hd2 hK2
  subst hk10
  have h0 : repTypes.getD 10 0 = 0 := rfl
  omega

end Ident

end CertificateChecks.KernelO8.Q125

end
